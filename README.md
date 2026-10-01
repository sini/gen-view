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
beside it. Each `shadowed` record is the losing contribution plus `orders`: every component of the
effective order that holds a pair shadowing it, `"orderMark"`, `"order"` or both, never empty — as
`withheld`'s `marks` names every mark. A visible contribution carries no such field.

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
`directions` is derived, not added: `inbound` is the query over the labelled converse of the graph's
L edges after its boundary marks, so a mark withholds the same authored edge whichever way the
query walks.

A dedup collapse keeps its twins' dependency edges wherever it can read them. `==` is blind to string context, so data equal
under it may carry different store paths; the kept datum then carries the union of its twins'
contexts when it is a string, and under `byDatum` a non-string that would lose an edge is refused
by name (`ci/tests/dedup-context.nix`; the refusal is a known boundary, to be retired). The
walk stops at a coercion, at `__toString`, else `outPath`, so a context held beside one is an edge
it cannot read: under `byDatum` a collapse holding a coercible set that is not a derivation and has
attributes besides its coercion is refused by name, whatever those attributes carry. The check
reads attribute names, and `type` only of a set with an `outPath`; it forces no other sibling's
value, and it follows an `outPath` that is itself a set. A set typed
`"derivation"` with an `outPath` is exempt: it is compared by its `outPath`. `combines.setUnion`
collapses its elements under `==` too, and a STRING element carries its twins' contexts.

### Dedup and string context: the stated boundaries

Three collapses drop a twin's store dependencies silently. Each is a declared exception to the rule that
a result is "a value or a named refusal", and each retires once store dependencies become graph
edges, where dedup is a quotient that keeps every datum's edges.

**Under `byKey`, a collapse of `==`-equal NON-string data drops the collapsed twin's store
dependencies silently.** `byKey` addresses the key and never walks the datum. The union reaches a string kept
datum only, and a non-string datum's twins are never forced. Carrying the loss would need a walk of
datum content, and a walk bounded so that it refuses past its bound would refuse deep valid input.
gen admits no bound invented to limit cost. Pinned by
`…-drops-the-twins-edge-the-stated-boundary`.

**In `combines.setUnion`, a collapse of `==`-equal NON-string elements drops the collapsed twin's
store dependencies silently.** Reading a non-string element's edges is a walk of its content. The
union adds no walk to `unique`'s own `==`: it hands each non-string element on as `unique` returned
it, so where `==` meets the same value it takes its pointer-identity shortcut, and a pointer-shared
cyclic element or one with a lazily-throwing attribute contributed twice is a value. An edge walk
would overflow on the first and force the second. (`==` between elements that are not the same value
still compares them structurally, as it did before the rule.) A bounded walk is excluded on the same ground. This boundary
is pending an owner reading. Pinned by `…-set-union-non-string-collapse-drops-the-twins-edge-the-stated-boundary`.

**A context held beside a derivation's `outPath` (`drv // { extra = <store path>; }`) is dropped
silently** under `byDatum` and in the union. Nix `==` compares a derivation by its `outPath`, so the
collapse is licensed, and W3's refusal exempts derivations so that ordinary packages stay admitted.

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

**Both nesting modes place a result under its own name — `path ++ [ name ]`, not `path` — and this
is an intentional divergence from den v1, not an open gap.** v1's placement wrote exactly `path`
for every arm; here, `nest` and `nest-verbatim` append the name so that distinct named
contributions stay distinct under one path, while `merge` still lands exactly at `path` and is
where v1's exact-at-P shape stays expressible. The mode is the `M` of the `(S,T,P,M)` edge
grammar; mapping a v1-shaped tree onto this placement is an adapter's job (a lens over the placed
result, in the sense of Foster et al. 2007), not a fourth mode here.

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
  marks;                 # required: node id → [ { name; admits; } ]; `_: [ ]` for none
  localShadowsImport; importShadowsParent; transitiveImports;
}                        # ⇒ ONE datum, or the authority's refusal

neededBy {
  engine;                # the authority — must publish `queryReverse`
  name; wellFormed;      # the result name, and σ
  project;               # π
  marks;                 # required, as above
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

**The boundary marks compile at the authority's accessor, as the fail-closed floor of every query's reachability.** The authority walks a bounded
record in which `graph.boundedBy` has classified each `imports` edge and each `parent` edge at the
node it leaves; what a mark refuses is absent, and `withheld self id` names the marks that withheld
it. `neededBy` reads the same forward bound, so a mark at the importer removes it from the gather
and a mark at the gathered node does not.

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

`edgeSortKey` and `renderEntry` are published over **any** entry, and a hand-built one reaches them
without passing `traceEntryOf`. They split on what each owes its reader:

- **`edgeSortKey` refuses by name.** A sort key must be injective on what it orders, so a field it
  reads (target, path, source, mode, kind, and their names) that is absent, is not a record where a
  record belongs, carries an arm other than `root` or `output`, or is not a name — a function, a set,
  an `outPath`/`__toString` set that would key as the string it coerces to — is refused with a
  catchable `gen-view.edgeSortKey:` (or `.sourceKey:`, `.targetKey:`, `.pathKey:`) error. The
  witness distance and word are not read, so the key does not judge them.
- **`renderEntry` discloses by type and never coerces.** Each field renders by `builtins.typeOf`: a
  string, a number and a path as values, anything else as its marker (`‹set›`, `‹lambda›`, `‹list›`,
  `‹bool›`, `‹null›`, and `‹absent›` for a missing field). It is total over values, so one malformed
  entry never hides the rest of a `renderTrace`; `renderTrace` itself refuses by name anything that
  is not a list. What a display may still do is render two distinct values alike (two sets, a path
  and its string); distinct entries stay distinct in the trace and its fingerprint.

## Head positions and the joined trace

`headPositions { heads; structure; root; data; }` lifts a structural scope graph to one copy per
declared **head letter**, so every datum's path word is a head letter followed by a structural
word. Fig. 1's visibility order decides at the **first** position where two words differ, so a
ranked letter at the head is compared before any structural letter and structure decides only
between words sharing one head. The same letter at the tail is compared only after the structure
has already differed: the rank is never read, the answer is plausible and wrong, and nothing is
refused. The construction makes that placement unwritable rather than detected — a fresh root is
the only scope with a head edge, position `⟨s, h⟩` exists for every structural scope `s` and head
`h`, and a structural edge only ever joins two positions of one head.

The door is what keeps it true, and each refusal is by name:

- **`heads` is an ordered list of distinct strings, one rank per letter.** Two head letters sharing
  a rank have no spelling, because a list position holds one letter; a list inside the list, a
  non-list, an empty list, a letter named twice and `$` (the end-of-path label) are all refused.
- **A head letter that is also a structural letter is refused.** A structural edge carrying it
  would put a ranked letter inside the structural word, which is the tail placement again.
- **A datum enters a position only through `data`, under a declared head letter.** The structure's
  own data and any edge that is not a structural letter are refused, and so is a datum under an
  undeclared head.

It returns data: `graph` (the product scope graph), `admission`, `order` and `orderMark` (the mark
ranks each head letter in its own layer in list order, then every structural letter with `$` in
one layer, so within one head the query order decides), `owners` (each position back to its
`{ scope; head; }`), `scopes` (the structure's own) and `position s h` (a position's id). There is
no caller-mark parameter: the order mark is the head ranks, outermost, and one tied structural layer.

`joinedTrace { relation; placement; positions; innerOf; }` is the trace of a relation
materialized over `headPositions`, each entry joined to the record its contributor's **own**
evaluation keeps. The head letter is already the first letter of the entry's word and the
contributor is the position's owner, so the substrate side needs no new fact; what happened inside
the contributor is the caller's to supply. `innerOf scope` returns that scope's record for the
channel — opaque except for `scope`, `loc`, and `band` (the value moved) or `reason` (it did not) —
or `null` for a scope that contributes nothing. It returns three halves:

- **`joined`**: one `{ entry; contributor; band; inner; }` per trace entry, where `band` is the
  head letter and `inner` is the contributor's record.
- **`unset`**: every structural scope's record of a value that did not move. Every scope is asked,
  not only the trace's, because a scope that did not move puts nothing in the relation and the
  substrate's own record never mentions it.
- **`unaccounted`**: a moved record whose scope owns no datum among the relation's `contributions`,
  `shadowed` or `dropped`, kept intact. It is **recorded, not refused**: it covers a datum never
  placed, a relation materialized from another root and a datum the definition's `wellFormed`
  rejected, which is lawful and which the relation records nowhere. `withheld` is not read: its
  rows are blocked edges keyed by the edge's source, so a row at a position witnesses no datum there.

`innerOf` is a caller-supplied function, so each failure mode has a door: a missing or non-record
result for a contributor in the trace, a record whose `scope` is another contributor's (a
mis-keyed join) and a record carrying both `band` and `reason` are each refused by name; a throw
propagates as the caller's own error.

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
