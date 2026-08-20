# gen-view — agent cheatsheet

## Scope

The substrate's **derived-view constructor**. A view definition is plain data; a view relation is
the named result of materializing it over a scope graph. Registry, topology, channel, role and
movement are **one construction** at **three key shapes** — five names, one `define`, and two pairs
that deliberately coincide (`movement` ≡ `channel`; `registry` ≡ `role` modulo the caller's field
name). Do not "differentiate" them to make a tidier claim true.

Two inputs: `gen-prelude` and `gen-graph`. `lib` is a function of both.

> ★★ **THE LIBRARY NAME IS TEMPORARY; THE CONSTRUCT NAMES ARE NOT.** `gen-view` is a way-station —
> its constructs fold into a consolidated library later and become a **sublibrary** of a larger
> domain library. The container dissolves; the constructs descend into a namespace and persist. So
> **construct boundaries carry the design weight** and every construct name is grounded at a
> primary. Do not treat this container as a stable home, and do not weaken a construct name on the
> grounds that the library is provisional.

## Not this library's job

| Need                                                                                         | Owner                                                                                                                                                               |
| -------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Answering questions about structures without building or holding them                        | `gen-select` — its signature is that it never builds or holds. This library **builds and holds** a materialized result; folding either into the other is misscoping |
| The labelled walk, the Brzozowski derivative kernel, the boundary accessor, Kahn's algorithm | `gen-graph`. This library **composes** them and reimplements none of them                                                                                           |
| The ordered contribution fold's shipped shape                                                | `gen-scope.foldContributions` states the law in its own header. This library **re-derives the shape**, never the implementation                                     |
| Minting an identity                                                                          | `gen-identity`. Nothing here mints                                                                                                                                  |

## The published surface, by layer

**Raw calculus** (the five, each a named export): `edgeLabels` `labelWellFormedness` `labelOrder`
`dataOrder` `relations` — plus `carrier`, `scopeGraph`, `relationLookup`, and `carrierElements` as
the checkable enumeration of the five.

**Declaration**: `viewDefinition`, `definitionFields`, `compositionFields`, and the closed
enumerations `combines` `tieSets` `dedups` `directions` (with `combineArms` `tieSetArms`
`dedupArms`).

**Materialization**: `viewRelation`.

★★ **There is NO arrival-mode family, and do not reintroduce one.** `scopeGraph.data` is a PLAIN
COMPONENT — a list of `{ scope; relation; datum; }` — so **no traversal can change which datums are
in the component or where they are filed**, and there is nothing for the substrate to discriminate.
An earlier revision made `data` a function of the graph and then invented
`arrivalMode`/`authoredAt`/`emittedAt`/`severedAt` to catch what that let through; the owner
withdrew the divergence and the family retired with it. R17 is satisfied by the component shape:
authoring into the component IS the declaration.

★★★ **SCOPE THAT CLAIM WHEN YOU RESTATE IT — "walk-dependence is unsayable" is FALSE and was struck.**
Measured: `scopeGraph` forces `scope` and `relation` but never `datum`, and `labeled` is computable
from `edges` and `scopes` without `data`, so a caller can bind the graph and read it from inside a
datum. MEMBERSHIP and FILING are closed (both give infinite recursion, loudly); a datum's **VALUE**
is not, and it participates conditionally on graph shape. **That door is lawful and stays open:** a
datum's value is the author's and is not analysed — computing one IS authoring it, which is ADR-0024
arm F's explicit declaration. The defect arm F names is mechanical re-emission by the SUBSTRATE, and
the substrate performs one gather and consults no accessor. Do not "fix" the open door; do not
widen the claim back.

**Accumulator + ordering**: `readsOf` `writesOf` `unit` `accumulatorRelation` `accumulatorOrder`
`orderedFoldOf` `cell`.

**Families beside the declaration**: `placement` · `transform`.

**Oracle cluster**: `trace` `traceEntryOf` `renderTrace` `renderEntry` `edgeSortKey` `hashTrace`.

★ **Fingerprint a topology with `hashTrace`, never with `edgeSortKey`.** The key is a `" | "`-join
over free strings, so a component carrying the separator shifts the field boundaries and two
structurally distinct entries render one key — it is **not preimage-injective**, and anything keyed
on it can be forged by that shift. `hashTrace` is `sha256` over the canonical JSON of the trace,
where every component sits under its own name; entries that collide on the key still separate there.
The collision only degrades `trace`'s **primary** order to a tie, which the canonical-JSON secondary
resolves.

**Compositions**: `compositions.{ movement, channel, registry, topology, role }`.

## Rules that will bite you

- **Nothing is defaulted.** Every field of a view definition is required, and so is `marks` at the
  materialization — "no marks" is `_: [ ]` written down. If you are about to add a default, the
  answer is a refusal instead.
- **The competition key and the distance rule are mandatory** for measured reasons: a per-node key
  default makes competition vacuous, and a defaulted distance rule is a semantics nobody wrote.
- **`L` is structural-only.** Content lives in `R` and is reached at the path's end. An admission
  expression naming a relation is refused at construction.
- **The label order is total over the alphabet.** An unranked letter is refused by name rather than
  taking a bottom rank nobody declared. `layers` is a list of ranks, so two letters can be
  incomparable — that is how "no specificity" is said.
- **No identifier may be named `materialize`.** The act has no term at any archived primary;
  `viewDefinition` and `viewRelation` do (Manchanda & Warren, printed 381), and the update-versus-
  maintenance narrowing travels with that citation everywhere it appears.
- **The fold may not reorder or dedup by rank.** `gen-graph.queryFold` is NOT a successor to it: it
  folds over the sorted answer set and wants a commutative-idempotent monoid.
- **The ordering door must never accept the raw labelled-edge accessor.** The input type is the
  stratification, and relaxing it reads like a query-surface change while being a semantics change
  that does not throw.

## Tests

```
nix-unit --flake ./ci#tests        # the suite
nix-unit --flake ./ci#testsError   # cells whose subject is an error MESSAGE
```

Both need running. Error-message cells cannot live in `flake.tests`: the batch asserter behind
`checks.default` forces every `expr` unconditionally, so a throwing `expr` crashes that gate rather
than failing it. `ci/tests-error.nix` sits outside `./tests` **structurally**, not by convention.

`ci/fixture.nix` is the shared fixture — one carrier, one scope graph, one declaration — and lives
outside `./tests` so `import-tree` does not read it as a suite. Build variants with
`f.mkDefinition { <one field> = …; }` so a fixture and its mutant differ in exactly one respect.

★ **Two Nix lambdas are never equal, not even against themselves** (measured: `{ v = d.f; } == { v = d.f; }` reads false for one and the same attribute). Comparisons over constructed values must
exclude raw-function fields and check those by name. Element attrsets compare fine when both sides
hold the same constructed element.
