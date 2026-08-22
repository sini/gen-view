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

## What this library INHERITED, and from where

**Most of the surface below arrived by RETIREMENT, not by original construction here.** It is
recorded because the sheet is where a reader asks where `hashTrace` came from, and a construct with
no provenance reads as this library's invention — which loses both the ruling that put it here and
the archived original a comparison can still be run against. Both source repositories are
**orphaned for reference** under ADR-0031 §3's F3 pattern — marked, never cut, so every export named
below still evaluates there. **Bind the names in this column; route no work to those repositories.**

| What arrived                                                                                                    | From                                                                                                                        | Where it lives here                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| --------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| The content-movement contract — the `(S,T,P,M)` edge algebra, edge-set derivation, Kahn-ordered materialization | `gen-edge`, archived. ADR-0010 §3, which gained `gen-view` as its **fourth destination** on 2026-08-20                      | **Twelve of that library's eighteen exports name a construct here.** `edge` **splits** across `viewDefinition`'s `root`/`direction`/`admission`/`channel` and `placement.place`; `modes` → `placement.modes`; `targets` → `placement.targets`; `defaultFold` → `compositions.movement` + `placement.place`; `edgesFor` → `viewDefinition.root` → `viewRelation`'s contributions; `toposort` **splits** into `accumulatorRelation` (the relation) + `accumulatorOrder` (gen-graph's Kahn arm, reached by name); `materialize` → `viewRelation`'s value + `placement.place` + `orderedFoldOf`; `project` dial by dial → `relationLookup` · `dedups` · `viewRelation`'s `marks` · `scopeGraph.scopes`; `readsOf`, `writesOf` and `placement.setAttrByPath` keep their names |
| Scoped channels and the dataflow algebra — map/filter/fold/scan/route/tee, provenance                           | `gen-pipe`, archived. The same ADR-0010 §3 ruling, on the same day                                                          | **Twelve of that library's seventeen exports name a construct here** — `channel` → `compositions.channel`, the deriving operators → `transform`, `provenanceOf`/`traceOf` → the oracle cluster below. ★ `sel` did **not** come here: it retired into `gen-select`, which consumers now bind directly                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| The parity-oracle cluster — `trace` `traceEntryOf` `renderTrace` `renderEntry` `edgeSortKey` `hashTrace`        | `gen-edge`. It retired **last**, after movement AC-7 ran, because it was the instrument validating the spec that retired it | The same six names. `hashTrace` landed here at `6536ee9` as the cluster's sixth member. ★ AC-7's verdict **re-scoped** the instrument rather than ratifying it: the frozen edge trace `E` is topology evidence, **not acceptance authority**, because the run measured two executions with different answers sharing a byte-equal fingerprint. Do not cite `E` as an acceptance oracle                                                                                                                                                                                                                                                                                                                                                                                   |

★ **WHAT DID NOT ARRIVE — read this before assuming an inheritance covers a case.** Five surfaces are
**HELD** at the retiring libraries: no construct here holds them, and minting one is a design
decision rather than a lookup. From gen-edge — `sources.synthesize` and `sources.rewalk` (this
library carries **no source-arm vocabulary**; `rewalk` is live in den v1, where three parity gates
use it) and `project`'s `classInject` dial. From gen-pipe — `contribute`, ruled to a producer
declaration no document defines, and `deferred`, assigned to the eval-boundary crossing that the
landed crossing does not carry. Separately, gen-pipe's `join` retired as a **caller-side
composition** — no single construct here performs the fan-in — and `consume` **split**, its
class-discipline half ruled to a delivery-class realization surface not yet extracted.

## The published surface, by layer

**Raw calculus** (the five, each a named export): `edgeLabels` `labelWellFormedness` `labelOrder`
`dataOrder` `relations` — plus `relatumLabels`, `carrier`, `scopeGraph`, `relationLookup`, and
`carrierElements` as the checkable enumeration of the five.

★★ **`relatumLabels` IS A PUBLISHED CONSTRUCTOR AND IS NOT A SIXTH CARRIER ELEMENT** — do not read
`carrierElements` as the whole raw layer, and do not "complete" the enumeration by adding it. `Λ` is
the **relatum-role population**: a binding is a reified relation whose incident edges reach the edge
set carrying the roles its relata play, so the population is real and has to be declarable. It
**indexes nothing in the carrier** — admission is indexed by the binding's kind, the relation `r`,
never by a role label — which is why `carrierElements` stays five while the export count does not.

- **Required, not optional.** `carrier` refuses without it by name; a graph with no reified bindings
  says so by declaring `relatumLabels { names = [ ]; }`. An empty `Λ` is lawful where an empty `R` is
  refused — `R` empty means (NR-Rel) reaches no datum at all, `Λ` empty is the commonest graph.
- **Λ-labelled edges are HELD AND NOT WALKED.** `Λ ∩ L = ∅` and `labelWellFormedness` refuses every
  literal outside `L`, so the derivative of any admission expression with respect to a role label is
  the empty state and the walk prunes there. The inertness is structural, not promised.
- **The classification of an edge label is total over three populations**, `L` · `R` · `Λ`:
  `scopeGraph` refuses a label in none of them, and `carrier` enforces all three disjointness pairs
  separately, each with its own refusal.

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

**Reference resolution**: `referenceResolution`, with `referenceResolutionFields` as the checkable
enumeration of its seven. A **defining query** whose compute is **TOTAL DELEGATION** to an injected
query authority. The term is the primary's own — Néron et al. 2015 names *"reference resolution"* as
a **rule of the resolution calculus** (Fig. 3 rule (X), and rule (X′) of Fig. 19). It is **not**
`referenceAttribute`: Hedin 2000's reference attribute takes *"the (unique) identity of the denoted
node"* as its value, where this construct's value is the caller's **projection of the resolved
node's datum** — so that term would be true at the source and false here.

★★ **THE AUTHORITY IS A FIELD, AND THAT IS WHAT KEEPS THIS LIBRARY EVALUATOR-FREE.** `engine` is
injected into the constructor, so `lib/` acquires no evaluator and `flake.nix` no edge onto one —
gen-scope is a **ci-only** input, on the same terms as nixpkgs, and
`ci/tests/reference.nix` asserts that absence over `lib/`'s own source with a positive control
rather than leaving it to prose. Do not "simplify" by importing the authority.

★★★ **THERE IS NO `codomain` FIELD AND DO NOT ADD ONE.** A literal such as `codomain = "atMostOne"`
would be a constant *here* about a fact owned *there*, and it would be **false in the sense it
claims**. D < I < P orders the three **sorts**; **nothing orders candidates among the imports.** The
delegate disposes a multi-candidate import set by the **runtime type of the projected datum** — an
attrset shadow-folds across *every* candidate, anything else takes the first in the caller's own
declared imports order. So the **cardinality is one and the provenance is not**: the value returned
is not in general the datum of any one node. Pinned by
`reference.test-a-multi-candidate-import-set-is-disposed-by-the-authority`, whose attrset arm
expects `{ a = 1; b = 2; }` — a value present at **neither** contributing node. The fact is selected
inside the delegate's closure on a runtime type, so no constructor can derive it and no
construction-time check can know it; it is **pointed at**, never re-spelled.

★ **The relation is NOT declared here**, though `viewDefinition` requires one: the only honest
source for the name is the delegate's traversal vocabulary, which is a private module there, so a
`relation` field would be an **unchecked** re-spelling — the drift shape this ecosystem has closed
twice. And **`wellFormed` and `project` are two fields because the defining query has two
operators**; fusing them back into one predicate makes `null` mean both *"not a binding here"* and
*"the value"*, which is the defect `requireNonNull` refuses.

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
