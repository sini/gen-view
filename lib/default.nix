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
# nothing to discriminate. `data(G)` is a COMPONENT of the graph value (Fig. 1), so a datum is in
# it or it is not and no traversal can put one there — WALK-DEPENDENCE IS UNSAYABLE RATHER THAN
# DETECTED. An earlier revision made `data` a function of the graph, which made the hazard sayable,
# and then invented a discriminator to catch what fell through; the divergence is withdrawn and the
# discriminator retired with it. R17's shape requirement — a contribution competes only if declared
# — is met BY THE COMPONENT SHAPE: what competes is exactly what is in `data`, the only way in is
# for an author to write it there, and a walk answer is refused in a data position by name.
# · `placement`, `setAttrByPath`, the placement modes and the terminal sink: ruled into a fourth
#   destination with no name and no owner, which is this library — kept as a construct family
#   BESIDE the declaration, never as declaration fields.
# · `transform.{ map, scan, over }`: content transformation, excluded from the declaration by
#   construction and homed here rather than dropped.
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

  # ── THE ORACLE CLUSTER — expressible HERE before it retires THERE ───────────────────────────
  inherit (traceLib)
    trace
    traceEntryOf
    renderTrace
    renderEntry
    edgeSortKey
    ;

  # ── THE NAMED COMPOSITIONS ──────────────────────────────────────────────────────────────────
  inherit (compositionLib) compositions;
}
