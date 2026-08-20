# ARRIVAL MODE — DERIVED, never declared; and a walk-emitted value's participation is
# INEXPRESSIBLE rather than filtered.
#
# ★★ THE HEADLINE IS THE RULED ONE, AND THE FAMILIAR PHRASING IS RETIRED. Struck, quoted so it is
# not re-introduced: *"a contribution competes only if declared."* That framing is a DECLARATION
# REQUIREMENT IN THE SUBSTRATE, and the standing rule is that a dependence fact is DERIVED unless
# derivation is proven impossible, with the burden asymmetric and the proof written at the
# declaration — an assertion that a fact is unanalysable is not a proof of it. What is asked for
# is not "make contributions declared" but "make arrival mode DERIVABLE, and make a walk-emitted
# value's participation INEXPRESSIBLE".
#
# ★★ WHY THE DISCRIMINATOR IS DERIVABLE, WHICH IS THE WHOLE GROUND. The defect this guards against
# was never an intent — it was a MECHANICAL RE-EMISSION: a node walk re-emitting the host's
# channel-named keys at the visited scope. That is a STRUCTURAL FACT ABOUT HOW THE VALUE ARRIVED,
# not a fact about what anyone meant. The theory's own split agrees: a contribution's SORT is
# derivable, its INTENT is not, and this asks only for the former.
#
# ── THE MECHANISM, AND IT IS THE CALCULUS'S OWN PROPERTY RESTORED ────────────────────────────
# In van Antwerpen 2018's Fig. 1 a scope graph is `⟨scopes, edges, data⟩` and `data(G)` is a
# COMPONENT of G. (NR-Rel) reads `s′ —r→ d ∈ data(G)`: membership in the data component, which is
# walk-independent BY DEFINITION — no traversal can put a datum there. In a substrate that reaches
# the component through an accessor, walk-dependence becomes sayable. So:
#
#   a datum at scope `s` is AUTHORED     iff it is still there when `s`'s OUTGOING EDGES ARE CUT
#   a datum at scope `s` is WALK-EMITTED iff it is present only while those edges stand
#
# Severing `s`'s out-edges removes exactly the walk that a re-emitting accessor consults, and
# nothing else: the data component is a function of the graph, so cutting the edges is the whole
# of the intervention. An accessor that ignores the graph — the ordinary, authored case — answers
# identically either way, which is why the ordinary case pays no semantic price.
#
# ★★ AND THE PARTICIPATION IS INEXPRESSIBLE, NOT FILTERED. `authoredAt` is the ONLY gather this
# library's materialization performs: it reads `data (severed s) s` and never `data g s`. There is
# therefore no filtering step that could be forgotten, no flag that could be set wrong, and no
# widening a caller could reach for. What dies is the implicit side effect; the SEMANTICS the
# side effect produced stays fully available to an author who writes the value down, at the same
# position, where it competes normally.
#
# ★★ THE PROPERTY THIS PRESERVES IS ALREADY TRUE, WHICH IS WHY THE SUITE'S NEGATIVE ARM IS A
# HAND-CONSTRUCTED ADVERSARIAL FIXTURE. Measured across the gen family: there is no mechanical
# re-emission channel, so every contribution is already authored. This is NOT new machinery
# guarding a live defect — it is what keeps that property true BY CONSTRUCTION as the shapes that
# had one migrate in. By-construction over repair, in its exact sense.
#
# ★ THE UNSAFE REMEDY, NAMED SO IT IS NOT REACHED FOR: narrowing the admission expression cannot
# serve. A ruled instance admits one relation at distance 0, so an AUTHORED own-contribution and
# an INCIDENTAL one present ONE ADMISSION ATOM AT ONE DISTANCE and cannot be separated there.
# The inseparability is a property of admission-by-one-atom, not of the population the atom is
# drawn from: whether the remedy narrows an alphabet of letters or a set of relations, both
# arrivals still present the same atom at the same distance.
#
# ★ AND THE CONSTRUCTION IT MUST NOT LIMIT: a self-edge used to gather a facet is measured safe.
# Facet collection is the BASE TERM of a union with a self-excluding gather, so it never enters
# the gather and never competes — severing a scope's out-edges does not touch it.
{ prelude, graph }:
let
  inherit (prelude) filter elem;
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  inherit (refusal) refuse fields;
  inherit (carrierLib) elementOf;

  # The graph with one scope's OUT-EDGES cut, and nothing else changed. The node set is untouched,
  # so every global surface still sees the same domain; only the walk out of `scope` is gone.
  severedAt =
    labeled: scope:
    labeled
    // {
      labeledEdges = id: if id == scope then [ ] else labeled.labeledEdges id;
    };

  # `authoredAt g scope` — the datum entries in `data(G)` at `scope`, in the calculus's sense:
  # those that do not depend on the walk out of it. This is the library's ONLY gather.
  authoredAt =
    g: scope:
    let
      gg = elementOf "authoredAt" "graph" "scopeGraph" g;
    in
    gg.data (severedAt gg.labeled scope) scope;

  # `emittedAt g scope` — what the accessor answers with the graph whole. Published so a caller can
  # SEE the difference the discriminator makes, and so the adversarial fixture that proves the
  # discriminator is not vacuous has something to compare against. It is deliberately NOT what any
  # materialization reads.
  emittedAt =
    g: scope:
    let
      gg = elementOf "emittedAt" "graph" "scopeGraph" g;
    in
    gg.data gg.labeled scope;

  # `arrivalMode { graph; scope; entry; }` → "authored" | "walk-emitted".
  #
  # ★ THE THIRD ANSWER IS A REFUSAL, NOT A THIRD MODE. An entry present in NEITHER reading is not
  # at that scope at all, and answering "walk-emitted" for it would let a caller's typo report a
  # structural finding. The mode is a question about a datum that is there.
  arrivalMode =
    args:
    let
      a = fields "arrivalMode" [
        "graph"
        "scope"
        "entry"
      ] args;
      g = elementOf "arrivalMode" "graph" "scopeGraph" a.graph;
      authored = elem a.entry (authoredAt g a.scope);
      emitted = elem a.entry (emittedAt g a.scope);
    in
    if authored then
      "authored"
    else if emitted then
      "walk-emitted"
    else
      refuse "arrivalMode" "the entry is not in the data component at scope '${a.scope}' under either reading, so it has no arrival mode; a datum that is not there did not arrive";

  modes = [
    "authored"
    "walk-emitted"
  ];
in
{
  inherit
    severedAt
    authoredAt
    emittedAt
    arrivalMode
    modes
    ;
}
