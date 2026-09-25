# gen-view — the substrate's derived-view constructor

**Every derived view is a named materialized query result over the selector algebra.** Registry,
topology, channel, role and the aspect/entity classification are **one construction under different
names**; movement is the first composition over it, not the calculus.

The five published names are **one construction at three key shapes** — the channel (`movement`,
`channel`), the scope (`topology`), and a caller-supplied coordinate (`registry`, `role`). Two of
those pairs coincide, deliberately: the counts are stated rather than rounded.

This library publishes that calculus **raw** and the compositions **on top of it**.

> ⚠️ **`gen-view` IS A TEMPORARY NAME AND A WAY-STATION.** Its constructs fold into a consolidated
> library later, where they become a **sublibrary** of a larger domain library. **No consumer should
> adopt this container as a stable home** — the hub's roster row carries the same marking. The
> CONSTRUCT names are not temporary: they descend into that namespace and are grounded accordingly.

## The two layers

| layer            | what it publishes                                                                                                                                                                                                                                         |
| ---------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **raw calculus** | `edgeLabels` (L) · `labelWellFormedness` (E) · `labelOrder` (\<) · `dataOrder` (k) · `relations` (R), plus `relatumLabels` (Λ — a **required** field of `carrier` and deliberately **not** a sixth element), `carrier`, `scopeGraph` and `relationLookup` |
| **compositions** | `compositions.{ movement, channel, registry, topology, role }` — five names over one construction, at three key shapes                                                                                                                                    |

Publishing only the convenience composition **hides the calculus**, so a consumer needing a
different instance has to re-implement one. Here the rule is doubly load-bearing: the constructs
migrate and the container does not, so **a published calculus moves intact** where a
composition-only surface would have to be rebuilt.

## The carrier

`(L, E, <, k)` is a **narrowing** of van Antwerpen et al. 2018, *Scopes as Types*, Fig. 1
(printed 114:5) — not an extension of it. That figure's **four** visibility parameters are
`WFD ⊆ D`, `WFL ⊆ L*` ("defined as a regular expression"), `≤d ⊆ D × D` and `<l ⊆ L̂ × L̂`; gen names
one fewer, shipping WFD as the query's own predicate. The **fifth** element here is the one gen did
not have: the syntax parameter `relations r ∈ R`, "a set of relation names".

Under that arrangement a scope graph is `⟨scopes, edges, data⟩` with `Data ::= s —r→ d`, and the
relation is reached **once, at the end of the path**, by **(NR-Rel)**. So the walk is structural
throughout and content is filtered by WFD at the end — **a content name can never enter the label
word**, and `carrier` refuses an alphabet and a relation sort that overlap.

The regular-expression kernel is **cited, not reinvented**: `gen-graph.regex` steps Brzozowski
(1964) derivatives in a normal form, which is what bounds the derivative state set (Thm 5.2, over
the similarity of Def 5.2, whose ACI identities the normalization must *perform*).

## The name

> "A database view is a rule-defined relation that is made to appear as a base relation to the
> user."
> — Manchanda & Warren, *A Logic-based Language for Database Updates*, ch. 10 of Minker (ed.) 1988,
> **printed 381**, section *View Updates*.

Cite the **printed-381** form with its page: a near-duplicate at printed 365 reads "appear *like* a
base relation".

**The narrowing is part of the citation and is never dropped from it.** That chapter is
view-**update**, where the theory-terminology rider asked for view-**maintenance**, and no
maintenance primary is archived. It is a **definitional primary from adjacent literature and
nothing more**: this library *derives*; it **does not solve the update problem** — no update
translator, no add/delete translator, no update request accepted against a derived result.

`viewDefinition` and `viewRelation` are that primary's own terms. The **act** between them has no
term at any archived primary, so **no identifier here names it** — in particular there is no
`materialize`.

## Usage

```nix
{
  inputs.gen-view.url = "github:sini/gen-view";
}
```

```nix
let
  labels = view.edgeLabels { letters = [ "parent" "include" ]; };
  relations = view.relations { names = [ "import" "expose-in" "broadcast-in" "policy" ]; };
  admission = view.labelWellFormedness { alphabet = labels; expression = "(parent|include)*"; };
  order = view.labelOrder {
    alphabet = labels;
    layers = [ [ "include" ] [ "parent" ] ]; # containment outranks ancestry
    endOfPath = -1;                          # stopping outranks continuing
  };

  definition = view.compositions.movement {
    channel = "settings";
    relation = "import";
    root = "leaf";
    direction = "outbound";
    inherit admission order;
    wellFormed = _: true;
    tieSet = view.tieSets.union;
    empty = [ ];
    combine = view.combines.listAppend;
    dedup = view.dedups.byDatum;
  };
in
view.viewRelation {
  inherit definition;
  graph = view.scopeGraph {
    inherit carrier;
    scopes = [ "leaf" "mid" ];
    edges = { parent = id: if id == "leaf" then [ "mid" ] else [ ]; };
    # the data COMPONENT — a value, never an accessor
    data = [ { scope = "mid"; relation = "import"; datum = [ "x" ]; } ];
  };
  marks = _: [ ];   # required: "no marks" is written down, never defaulted
  # Required on the same terms. The effective order at the competition is the LEXICOGRAPHIC PRODUCT
  # of this mark with the definition's own `order`, MARK OUTER — the query may refine INSIDE the
  # mark's ties and can never erase or reverse a pair the mark declares. The identity is the
  # one-layer order over L̂, as here, under which the effective order is the definition's exactly.
  orderMark = view.labelOrder {
    alphabet = labels;
    layers = [ [ "include" "parent" ] ];
    endOfPath = 0;
  };
}
```

The result carries `name`, `value`, `contributions`, `shadowed`, `withheld` and `dropped` — the
discarded set, the boundary diagnostic and every dedup drop, **inside** the result rather than
beside it.

## What is required and what is refused

**Every field of a view definition is required and total.** A defaulted field is a decision nobody
made and nobody can see, and two of the fields exist because their absence used to be filled in
silently:

- **the competition key is mandatory.** A per-node default makes competition *vacuous* — measured:
  under it a chain returns the gather-all answer with nothing shadowed, while the same query with
  the key written shadows two. The fix is a mandatory key, not a different default.
- **the distance rule is mandatory.** A defaulted rule is a semantics nobody wrote down.

Refusals **name what they refused** — the omitted field, the unranked letter, the undeclared
relation, the mark that withheld an edge, the tied contributions. An empty answer is never a
refusal. Every constructor field is checked where the element is **built**, not where a field is
first read. Content stays lazy, but a throwing value in a checked field fails at construction even
if nothing reads it (`decided`, `lib/refusal.nix`). A caller-supplied function's **result** does not
exist at construction, so it is checked where it is consumed instead (`returned`, beside
`decided`): a competition key, an edge accessor's list and its L-edge targets, a marks list, each
mark and its `admits` verdict, WFD's and σ's verdicts, and `over`'s elements are refused by name,
naming the function's role, its input and what it returned. A function destructuring named
formals where it is applied to a string or a list is refused at its door (`formalsOf`); `{ ... }:`
and a destructuring functor stay the evaluator's own abort.

The closed enumerations: `tieSets.{ union, refuse, orderedFold }` · `combines.{ listAppend, attrsShallow, setUnion }` (a set-semilattice combine declares its **ACC flag**, because that
condition is undecidable from an arbitrary combine) · `dedups.{ none, byDatum, byKey }` ·
`directions.{ outbound, inbound }`.

A dedup collapse keeps every dependency edge. `==` is blind to string context, so data equal
under it may carry different store paths; the kept datum then carries the union of its twins'
contexts when it is a string, and under `byDatum` a non-string that would lose an edge is refused
by name (`ci/tests/dedup-context.nix`; the refusal is a known boundary, to be retired). Under `byKey` the
union reaches a string datum only, so a non-string collapse stays silent, as it was before. The
walk stops at a coercion, at `__toString`, else `outPath`: a context held beside one is not read,
and its collapse stays silent.

## The data component, boundaries and ordering

- **`data(G)` is a plain component of the graph value**, exactly as Fig. 1 writes it: a list of
  `{ scope; relation; datum; }` triples, never an accessor and never a function. **No traversal can
  change which datums are in the component or where they are filed** — (NR-Rel) is a membership test
  against a value that existed before any walk began. Both of those doors are closed loudly: making
  a datum's presence or its filing scope a function of the graph is infinite recursion.
- **A datum's VALUE is the author's, and is not analysed.** A caller may compute one from the graph,
  and such a datum participates conditionally on graph shape. That is lawful and deliberate:
  computing a datum **is** authoring it, which is the explicit declaration the carrier rule asks for.
  What that rule forbids is **mechanical re-emission by the substrate**, and the substrate performs one
  gather, consults no accessor, and cannot re-emit. No constructor can tell a graph-derived thunk
  from a literal, and none tries.
- **R17's shape requirement is met by that shape, not by a field and not by a check.** "A
  contribution competes only if declared" holds because what competes is exactly what is *in* the
  component, and the only way in is for an author to write it there: **authoring into the component
  is the declaration**. A walk answer has no route in — the datum field set is closed to the three,
  so a contribution (which also carries its path, its residual admission state, its distance and
  its channel) is refused in a data position **by name**. Stripping it back to three fields is an
  act of authorship performed by a person.
- **There is no arrival-mode discriminator, and its absence is the design.** An earlier revision
  made `data` a function of the graph — which made walk-dependence *sayable* — and then invented a
  discriminator to detect what fell through. The divergence is withdrawn; the hazard is
  **inexpressible rather than detected**, so there is nothing to discriminate.
- **effective E = node marks ∩ declared admission.** Marks apply at the accessor, so the
  construction only ever *removes* edges: **widening is not forbidden, it is unsayable.**
- **the ordering door takes the materialized projection and rejects the raw labelled-edge
  accessor.** The input type *is* the stratification: a consumed query cannot observe a conditional
  edge, so a query's answer cannot decide whether an edge exists, and the negative cycle cannot be
  written. That is Apt, Blair & Walker's Definition 3 clause (2) obtained structurally.
- **`readsOf` / `writesOf`** build the accumulator dependency relation the schedule consumes; the
  sorter is `gen-graph.topoOrderKahn` (A. B. Kahn 1962). Bernstein 1966's **output independence is
  deliberately dropped** — two units may write one cell, and determinism comes from the canonical
  cell ordering rather than from the schedule.

## Beside the declaration, never inside it

`placement` (the three modes with dedup exemption as a placement property, the root target and the
terminal sink) and `transform.{ map, scan, over }` are **construct families**, not declaration
fields: folding placement or content transformation into the declaration would reconstruct the
released edge grammar under new names. `over` is the one operator that can **reorder**, so its
result reports whether it did.

A root target's `scope` and `channel` are non-empty strings. `placement.targets.root` refuses any
other value by name where the target is built, and `targetKey` and `writesOf` refuse a hand-built
`target` record the same way, because an element tag is a claim rather than a proof.

The same holds at **every** intake that admits an element by its tag. Each one re-checks the
element's structural fields by type, all the way down its nested elements, and refuses a forged one
by name (`elementOf`, `lib/elements.nix`). It never forces content: a view relation's `value`,
`contributions`, `shadowed`, `withheld` and `dropped` are checked by the reader that reads them. A
kind gen-view does not shape is tag-tested only, as before. `boundedWellDefinedSchedule` re-checks
gen-graph's declared-edges marker the same way and derives its edges from the checked `index`.
What this does not close is a forged field of the right type carrying the wrong value.

`placement.setAttrByPath` **was** part of that family and is **no longer exported**: the owner
ruled (2026-08-27) that the path writer/reader pair lands in **gen-prelude**, and every live
hand-roll converges on it. Use `gen-prelude`'s `setAttrByPath`, which additionally **refuses by
name** on a non-list path or a non-string segment where this one fell into a raw uncatchable
abort. `lib/placement.nix` keeps the declined position and its measurement.

## The two defining queries — `referenceResolution` and `neededBy`

Both are **defining queries over an INJECTED authority**, and both hold **no walk of their own**:
the compute is delegation and nothing else, which is what keeps this library evaluator-free. They
are two constructs over the two directions of one relation.

```nix
referenceResolution {
  engine;                # the authority — must publish `query`
  name; wellFormed;      # the result name, and σ
  project;               # π
  localShadowsImport; importShadowsParent; transitiveImports;
}                        # ⇒ ONE datum, or the authority's refusal

neededBy {
  engine;                # the authority — must publish `queryReverse`
  name; wellFormed;      # the result name, and σ
  project;               # π
  transitive;            # direct importers, or the reverse-import closure
}                        # ⇒ the LIST of contributions from the nodes that import the id
```

`neededBy` is the **projection of the datum at each node that imports an id**, among those the
predicate admits. The name is the owner's, ruled as the stated inverse of `includes`. It is **not a
base relation**: it is a *rule-defined relation made to appear as one* — Manchanda & Warren again,
printed 381 — which is what makes it a **view** and not an inverted lookup, an inverted lookup
being a materialized index with no name and no rule.

**Two constructs and not a `direction` field.** The forward arm answers one datum **or refuses**;
the reverse arm **gathers** and refuses nothing. One field would select opposite *dispositions* of a
different *shape*, which is a semantics chosen by a field value rather than stated as one defining
query. Where direction is only direction, one field is right — `viewRelation` has exactly that, and
its two arms share shape and share discipline.

**Not a second access path to `viewRelation { direction = "inbound"; }`** either. That one walks a
**held graph** from a **declared root** and holds a walk, a competition, a tie-set and a dedup; this
one reaches the **evaluator's live node set** through the injected authority, from the id handed
`compute` at force time.

An **empty gather is the ordinary case, never a refusal** — most nodes have no importers. The one
refusal that fires at materialization is `requireNonNull`: a node the predicate **admits** whose
projection is `null`. The authority reads that null as *no binding here*, so without the guard the
admitted contributor is **dropped from a list that still has something in it** — the answer stays
plausible and stays wrong.

**Order and duplicates are the delegate's, pointed at and not restated.** It neither sorts nor
deduplicates: a node reachable along two reverse paths **contributes twice**, because a reverse
gather counts contributions. A caller needing a set does that at its own call site.

The trace cluster — `trace`, `traceEntryOf`, `renderTrace`, `renderEntry`, `edgeSortKey`,
`hashTrace` — is the instrument that validates the spec that retires it, so it is expressible
**here** before it retires **there**. Entries are **identity only** and never carry resolved
content.

`hashTrace` is that instrument's topology fingerprint: `sha256` over the canonical JSON of the
trace, invariant under the order the edges were presented in and sensitive to which edges they are.
It is taken over the **trace** and never over the sort key, because the key is a projection — it
leaves out the witness distance and word, so two structurally distinct entries render one key. (Its
components are the JSON of their name tuples, so no name shifts a field boundary.) Canonical JSON
has no such route: every component sits under its own name. The collision degrades `trace`'s
primary order to a tie and the canonical-JSON secondary resolves it.

## Tests

```
nix develop ./ci --command ci                # the suite, guarded
nix develop ./ci --command ci --tests-error  # cells whose subject is an error message, guarded
nix-unit --flake ./ci#tests                  # the suite, unguarded
nix-unit --flake ./ci#testsError             # the error cells, unguarded
```

`ci` refuses when anything under a declared read root is unknown to git — any extension or name,
`_`-prefixed included — and the remedy is `git add` or a move. The bare `nix-unit` and
`nix flake check` forms are unguarded: they read a git-filtered copy of the tree, so an untracked
cell is silently absent and the run stays green.
