# gen-view — the substrate's derived-view constructor

**Every derived view is a named materialized query result over the selector algebra.** Registry,
topology, channel, role and the aspect/entity classification are **one construction under different
names**; movement is the first composition over it, not the calculus.

This library publishes that calculus **raw** and the compositions **on top of it**.

> ⚠️ **`gen-view` IS A TEMPORARY NAME AND A WAY-STATION.** Its constructs fold into a consolidated
> library later, where they become a **sublibrary** of a larger domain library. **No consumer should
> adopt this container as a stable home** — the ADR-0015 roster row carries the same marking. The
> CONSTRUCT names are not temporary: they descend into that namespace and are grounded accordingly.

## The two layers

| layer            | what it publishes                                                                                                                                       |
| ---------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **raw calculus** | `edgeLabels` (L) · `labelWellFormedness` (E) · `labelOrder` (\<) · `dataOrder` (k) · `relations` (R), plus `carrier`, `scopeGraph` and `relationLookup` |
| **compositions** | `compositions.{ movement, channel, registry, topology, role }` — one construction, differing in exactly one thing: the competition key                  |

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
  graph = scopeGraph;
  marks = _: [ ];   # required: "no marks" is written down, never defaulted
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
refusal.

The closed enumerations: `tieSets.{ union, refuse, orderedFold }` · `combines.{ listAppend, attrsShallow, setUnion }` (a set-semilattice combine declares its **ACC flag**, because that
condition is undecidable from an arbitrary combine) · `dedups.{ none, byDatum, byKey }` ·
`directions.{ outbound, inbound }`.

## Boundaries, arrival mode and ordering

- **effective E = node marks ∩ declared admission.** Marks apply at the accessor, so the
  construction only ever *removes* edges: **widening is not forbidden, it is unsayable.**
- **arrival mode is derived, never declared.** A datum is *authored* at a scope iff it is still in
  the data component when that scope's out-edges are cut, and *walk-emitted* otherwise. The gather
  reads only the walk-independent component, so a walk-emitted value's participation is
  **inexpressible** rather than filtered — which restores the calculus's own property, `data(G)`
  being a component of `G` and not a function of resolution.
- **the ordering door takes the materialized projection and rejects the raw labelled-edge
  accessor.** The input type *is* the stratification: a consumed query cannot observe a conditional
  edge, so a query's answer cannot decide whether an edge exists, and the negative cycle cannot be
  written. That is Apt, Blair & Walker's Definition 3 clause (2) obtained structurally.
- **`readsOf` / `writesOf`** build the accumulator dependency relation the schedule consumes; the
  sorter is `gen-graph.topoOrderKahn` (A. B. Kahn 1962). Bernstein 1966's **output independence is
  deliberately dropped** — two units may write one cell, and determinism comes from the canonical
  cell ordering rather than from the schedule.

## Beside the declaration, never inside it

`placement` (the three modes with dedup exemption as a placement property, `setAttrByPath`, the
root target and the terminal sink) and `transform.{ map, scan, over }` are **construct families**,
not declaration fields: folding placement or content transformation into the declaration would
reconstruct the released edge grammar under new names. `over` is the one operator that can
**reorder**, so its result reports whether it did.

The trace cluster — `trace`, `traceEntryOf`, `renderTrace`, `renderEntry`, `edgeSortKey` — is the
instrument that validates the spec that retires it, so it is expressible **here** before it retires
**there**. Entries are **identity only** and never carry resolved content.

## Tests

```
nix-unit --flake ./ci#tests        # the suite
nix-unit --flake ./ci#testsError   # cells whose subject is an error message
```
