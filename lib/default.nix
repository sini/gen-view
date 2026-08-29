# gen-view — the substrate's derived-view constructor.
#
# ★★★ THE NAME IS TEMPORARY, AND THIS IS THE FIRST THING THIS FILE SAYS. Owner, 2026: "keep
# gen-view for now; we're going to fold its constructs into a consolidated library later; gen-view
# is a temporary name." The roster entry carries a TEMPORARY / WAY-STATION marking, and that
# marking travels with every citation of the name: no consumer should adopt this container as a
# stable home.
#
# ★★ TEMPORARY IS NOT THROWAWAY. Owner, same day: "it should still be grounded -- the lib will be
# a sublibrary of a larger domain library." The name DESCENDS INTO A NAMESPACE rather than
# dissolving, so the theory-terminology rider applies IN FULL and is not deferred — and it reaches
# EVERY CONSTRUCT NAME, not only the library's. Which is why the term is grounded:
#
#     Manchanda & Warren, "A Logic-based Language for Database Updates", ch. 10 of Minker (ed.)
#     1988, PRINTED 381, section *View Updates*:
#       "A database view is a rule-defined relation that is made to appear as a base relation
#        to the user."
#
#   ★ Cite the printed-381 form WITH its page: a near-duplicate at printed 365 reads "appear LIKE
#     a base relation", and without the page the citation is ambiguous.
#   ★ THE NARROWING IS PART OF THE CITATION AND IS NEVER DROPPED FROM IT: that chapter is
#     view-UPDATE where the rider asked for view-MAINTENANCE, and no maintenance primary is held.
#     It is cited as a DEFINITIONAL PRIMARY FROM ADJACENT LITERATURE AND NEVER AS MORE.
#     THIS LIBRARY DERIVES; IT DOES NOT SOLVE THE UPDATE PROBLEM — no update translator, no
#     add/delete translator, no update request accepted against a derived result.
#
# ── THE TWO PUBLISHED LAYERS, AND THE RAW ONE CARRIES THE DESIGN WEIGHT ─────────────────────
# Owner, verbatim: "The libraries should expose the raw calculus where feasible, as well as the
# compositions on top of it." Here that is doubly load-bearing, because the CONSTRUCTS migrate into
# a consolidated library and the CONTAINER does not: construct boundaries carry all the design
# weight and the container carries none. A PUBLISHED CALCULUS MOVES INTACT; a composition-only
# surface would have to be rebuilt at the fold.
#
#   RAW      `edgeLabels` (L) · `labelWellFormedness` (E) · `labelOrder` (<) · `dataOrder` (k) ·
#            `relations` (R) — the five, plus `carrier`, `scopeGraph` and `relationLookup`
#   COMPOSED `compositions.{ movement, channel, registry, topology, role }` — FIVE NAMES over ONE
#            construction, instantiated at THREE key shapes (the channel, the scope, a
#            caller-supplied coordinate). `movement` and `channel` are the same instantiation and
#            `registry` and `role` are the same shape under different caller vocabulary; the
#            counts are stated at `compositions.nix` rather than rounded to "one thing"
#
# ── WHAT ELSE LANDS HERE, AND WHY ───────────────────────────────────────────────────────────
# · `readsOf` / `writesOf` and the accumulator relation: they travel with the MATERIALIZATION
#   machinery, which is this library. The sorter already had a home; its INPUT did not.
#
# ★★★ AND WHAT IS DELIBERATELY *ABSENT*: THERE IS NO ARRIVAL-MODE DISCRIMINATOR, because there is
# nothing for the SUBSTRATE to discriminate. `data(G)` is a COMPONENT of the graph value (Fig. 1),
# so NO TRAVERSAL CAN CHANGE WHICH DATUMS ARE IN THE COMPONENT OR WHERE THEY ARE FILED. An earlier
# revision made `data` a function of the graph, which let the substrate's own accessor re-emit; the
# divergence is withdrawn and the discriminator that chased it retired with it.
#
# ★★★ THE CLAIM IS SCOPED TO PRESENCE AND FILING, AND SAYING MORE WOULD BE FALSE. Struck, quoted so
# the broader form is not restored: ~~*"WALK-DEPENDENCE IS UNSAYABLE"*~~. MEASURED, each door in its
# own evaluation — a caller can bind the graph and read it from inside a datum, because `scopeGraph`
# forces `scope` and `relation` but never `datum`, and `labeled` is computable from `edges` and
# `scopes` without `data`:
#
#   MEMBERSHIP — whether the datum is in `data` at all   → CLOSED, infinite recursion
#   FILING     — which scope it sits at                  → CLOSED, infinite recursion
#   VALUE      — the datum's content                     → OPEN, and it participates conditionally:
#                two graphs differing only in an edge that does not affect whether the datum's scope
#                is reached give `["admit"]` and `[ ]` under a WFD that admits one of them
#
# ★★ AND THE OPEN DOOR IS LAWFUL, WHICH IS WHY IT IS SCOPED RATHER THAN CLOSED. A datum's VALUE is
# the AUTHOR'S and is not analysed: a caller writing `datum = <expression over the graph>` has
# AUTHORED that content explicitly, which is exactly ADR-0024 arm F's *declared explicitly rather
# than as an implicit side effect*. No constructor can distinguish a graph-derived thunk from a
# literal, and none should try — what the arm F defect names is MECHANICAL RE-EMISSION BY THE
# SUBSTRATE, and the substrate here performs one gather, consults no accessor, and cannot re-emit.
#
# R17's shape requirement — a contribution competes only if declared — is met BY THE COMPONENT
# SHAPE: what competes is exactly what is in `data`, the only way in is for an author to write it
# there, and a walk ANSWER is refused in a data position by name.
# · `placement`, the placement modes and the terminal sink: ruled into a fourth destination with no
#   name and no owner, which is this library — kept as a construct family BESIDE the declaration,
#   never as declaration fields. `setAttrByPath` arrived with them and has since retired to
#   gen-prelude by a later ruling (2026-08-27); `placement.nix` records that reversal.
# · `transform.{ map, scan, over }`: content transformation, excluded from the declaration by
#   construction and homed here rather than dropped.
# · `referenceResolution`: a DEFINING QUERY over an INJECTED authority, ruled in here rather than
#   swept in by proximity. It is the one construct of the retiring resolution wrapper with a live
#   external consumer, and it lands as a construct BESIDE the declaration for the same reason
#   `placement` does — it declares a query and holds no walk, so it is not a `viewDefinition` and
#   not a sixth composition. Its compute is TOTAL DELEGATION; this library acquires no evaluator
#   and no dependency edge onto one, because the authority arrives as a field.
# · the trace cluster: it is the instrument that validates the spec that retires it, so it must be
#   expressible here BEFORE it retires there.
#
# ── WHAT THIS LIBRARY IS NOT ────────────────────────────────────────────────────────────────
# NOT A MOVEMENT LIBRARY: a movement-specific library would build ONE INSTANCE of a general
# construction and force registry, topology, channel and role to duplicate or retrofit it —
# coupling-through-misscoping arriving before the library exists.
#
# NOT FOLDED INTO THE SELECTOR ALGEBRA, and the reason is measured: that library's signature is
# that it ANSWERS QUESTIONS ABOUT STRUCTURES IT NEVER BUILDS OR HOLDS, where this construction
# BUILDS AND HOLDS a materialized result. Folding it in is the same misscoping in the other
# direction. ⇒ A defect in the selector algebra is a defect in EVERY view, which is a reason to
# keep that algebra separate and load-bearing, not to absorb it.
{ prelude, graph }:
let
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  enums = import ./enumerations.nix { inherit prelude; };
  definitionLib = import ./definition.nix { inherit prelude graph; };
  relationLib = import ./relation.nix { inherit prelude graph; };
  orderingLib = import ./ordering.nix { inherit prelude graph; };
  placementLib = import ./placement.nix { inherit prelude; };
  transformLib = import ./transform.nix { inherit prelude; };
  referenceLib = import ./reference.nix { inherit prelude; };
  traceLib = import ./trace.nix { inherit prelude; };
  compositionLib = import ./compositions.nix { inherit prelude graph; };
in
{
  # ── THE RAW CALCULUS ────────────────────────────────────────────────────────────────────────
  inherit (carrierLib)
    edgeLabels
    labelWellFormedness
    labelOrder
    dataOrder
    relations
    carrier
    scopeGraph
    relationLookup
    ;

  # ★ Λ — THE RELATUM LABELS, PUBLISHED AS A CONSTRUCTOR AND DELIBERATELY ABSENT FROM
  # `carrierElements`. A binding's incident edges DO reach the edge set, carrying the roles its
  # relata play, so the population is real and has to be declarable. It is NOT a carrier element:
  # admission is indexed by the binding's KIND — the relation `r` — and never by a role label, so
  # `Λ` indexes nothing in the carrier. The enumeration below stays FIVE for exactly that reason.
  inherit (carrierLib) relatumLabels;

  # THE ENUMERATION OF THE FIVE, as a checkable list rather than a count in a comment. A sixth
  # element cannot join the carrier without this list and the cells that quantify over it moving
  # in the same commit, which is the failure a number in prose cannot see.
  carrierElements = [
    "edgeLabels"
    "labelWellFormedness"
    "labelOrder"
    "dataOrder"
    "relations"
  ];

  # ── THE DECLARATION AND ITS CLOSED ENUMERATIONS ─────────────────────────────────────────────
  inherit (definitionLib) viewDefinition;

  # THE FIELD SETS, PUBLISHED AS ENUMERATIONS FOR THE SAME REASON `carrierElements` IS. Every
  # field is required and total, so "each omitted field refuses by name" is a claim that has to
  # quantify over something; a field added without a cell to omit it is the failure a hand-written
  # list of cells cannot see.
  definitionFields = definitionLib.required;
  compositionFields = compositionLib.common;
  inherit (enums)
    combines
    combineArms
    tieSets
    tieSetArms
    dedups
    dedupArms
    directions
    ;

  # ── THE MATERIALIZATION ─────────────────────────────────────────────────────────────────────
  inherit (relationLib) viewRelation;

  # ── THE ACCUMULATOR RELATION AND THE ORDERING DOOR ──────────────────────────────────────────
  inherit (orderingLib)
    readsOf
    writesOf
    unit
    accumulatorRelation
    accumulatorOrder
    orderedFoldOf
    cell
    ;

  # ── PLACEMENT — a construct family beside the declaration, never inside it ──────────────────
  placement = placementLib;

  # ── CONTENT TRANSFORMATION — likewise a family, and `over` reports its own reorder ───────────
  transform = {
    inherit (transformLib) scan over;
    map = transformLib.mapDatums;
  };

  # ── REFERENCE RESOLUTION — a defining query over an INJECTED authority, likewise a construct
  # beside the declaration ─────────────────────────────────────────────────────────────────────
  # ★ IT IS NOT A CARRIER ELEMENT and does not join `carrierElements`, which stays at five: it
  # indexes nothing in the carrier and declares no walk. It is not a sixth composition either — the
  # five compositions are instantiations of ONE construction over `viewDefinition` → `viewRelation`,
  # and this construct goes through neither.
  inherit (referenceLib) referenceResolution;

  # The field set, published as an enumeration for the same reason `definitionFields` is: "each
  # omitted field refuses by name" is a claim that has to quantify over something, and a field
  # added without a cell to omit it is the failure a hand-written list of cells cannot see.
  referenceResolutionFields = referenceLib.required;

  # ── THE ORACLE CLUSTER — expressible HERE before it retires THERE ───────────────────────────
  inherit (traceLib)
    trace
    traceEntryOf
    renderTrace
    renderEntry
    edgeSortKey
    hashTrace
    ;

  # ── THE NAMED COMPOSITIONS ──────────────────────────────────────────────────────────────────
  inherit (compositionLib) compositions;
}
