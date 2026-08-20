# THE ACCUMULATOR RELATION AND THE ORDERING DOOR.
#
# ── WHY THIS LIVES HERE ─────────────────────────────────────────────────────────────────────
# `readsOf` / `writesOf` travels with the MATERIALIZATION MACHINERY, and that machinery is this
# library. The evaluator library was measured COUNTER-INDICATED for it: its stated contract is
# "we do not build a scheduler, Nix is the scheduler", while `readsOf`'s only consumer is an
# explicit topological schedule built AHEAD OF the fold.
#
# ★ THE CONSEQUENCE THE RETIREMENT NEEDS STATED: the SORTER already has a home — Kahn's algorithm
# (A. B. Kahn 1962, CACM 5(11)) ships under its own name in gen-graph — but the accumulator
# DEPENDENCY RELATION it consumes is built here. The sorter having a home was never enough; its
# INPUT did not have one.
#
# ── THE DOMAIN LAW, STATED HERE RATHER THAN POINTED AT ──────────────────────────────────────
# Bernstein 1966's conditions: two units may execute in either order iff
#   I(A) ∩ O(B) = ∅   ·   I(B) ∩ O(A) = ∅   ·   O(A) ∩ O(B) = ∅
# over their input (read) and output (write) sets.
#
# ★★ THE RELAXATION IS DELIBERATE AND IS RECORDED WITH ITS COMPENSATION: THIS RELATION DROPS
# OUTPUT INDEPENDENCE. Two incomparable views MAY write the same cell — two contributions landing
# in one ⟨scope, channel⟩ bucket is the ordinary case, not the pathological one — and their
# relative order is left UNCONSTRAINED by the sort. Determinism does not come from the schedule; it
# comes from the accumulator's CANONICAL CELL ORDERING, where a cell's content is ordered by the
# producing definition's frozen sort key and NEVER by arrival. NO VALID SCHEDULE IS OBSERVABLE:
# readers see all of their writers (that is what the read arcs are for), and what they see is
# order-normalized before they see it. So the dropped condition is not a soundness debt — it is a
# condition whose purpose is discharged elsewhere, and it is written down here so that a later
# reader does not "restore" it and serialize every co-writing pair for nothing.
#
# ⇒ ONE ARC KIND: `B depends on A` iff `writesOf A` feeds a read in `readsOf B`.
#
# ── THE ORDERING DOOR, AND WHY ITS INPUT TYPE IS THE STRATIFICATION ─────────────────────────
# The door takes the MATERIALIZED result and never the raw labelled-edge accessor. That is not an
# ergonomic choice; THE INPUT TYPE *IS* THE STRATIFICATION:
#
#   a consumed query cannot observe a conditional edge
#     ⇒ a query's answer cannot decide whether an edge exists
#       ⇒ the `includes → ¬holds → includes` cycle CANNOT BE WRITTEN
#
# which is Apt, Blair & Walker's Definition 3 clause (2) obtained STRUCTURALLY rather than
# checked.
#
# ★★ RECORDED BECAUSE THE FAILURE IS SILENT. A relaxation of this input type READS LIKE a
# query-surface convenience and IS a semantics change: an unstratified program does not throw — it
# quietly has no total model, and every answer it gives is an answer about a model that does not
# exist. This library publishes NO ordering door that accepts the raw labelled-edge accessor, and
# the refusal below names that accessor specifically so the next reader meets the reason and not
# just the denial.
{ prelude, graph }:
let
  inherit (prelude)
    elem
    filter
    map
    unique
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  placement = import ./placement.nix { inherit prelude; };
  inherit (refusal) refuse fields choice;
  inherit (carrierLib) elementOf;

  # A CELL is the unit both sets range over: a ⟨scope, channel, SIDE⟩ bucket, rendered to a string
  # so set intersection is a comparison rather than a structural scan.
  #
  # ★★ THE SIDE IS LOAD-BEARING AND IS NOT BOOKKEEPING. A collector READS the input cells of the
  # scopes it gathered and WRITES an output cell at its own root — and those are DIFFERENT cells at
  # the same ⟨scope, channel⟩. Without the side, a view that gathers at its own root would read and
  # write one cell, and two such views at one root would depend on each other in both directions:
  # a flow-dependence CYCLE manufactured entirely by the model, on a pair that is perfectly
  # schedulable.
  #
  # What makes the relation non-trivial in the other direction is the NESTING placement: a nesting
  # arm's placed content joins the target root's INPUT cell, which is the bucket a collector rooted
  # there folds. That is the nest∘merge decomposition, and it is where a real producer/consumer arc
  # comes from.
  cell =
    scope: channel: side:
    "${scope}/${channel}@${side}";

  # ★ THE DOOR'S TYPE CHECK, WRITTEN AS ITS OWN BINDING BECAUSE EVERY ENTRY POINT HERE OWES IT.
  # A raw labelled graph is recognisable — it carries `labeledEdges` — so the refusal can say what
  # was handed in and why that particular value is the one this door exists to reject, rather than
  # reporting a missing tag and leaving the reader to work out which of their values was wrong.
  materialized =
    site: field: value:
    if builtins.isAttrs value && value ? labeledEdges then
      refuse site "field '${field}' is a RAW LABELLED-EDGE ACCESSOR; this door takes the materialized result and only that, because the input type is the stratification — a consumed query cannot observe a conditional edge, so a query's answer cannot decide whether an edge exists, and the negative cycle is unwritable rather than merely unwritten. An unstratified program does not throw; it quietly has no total model"
    else
      elementOf site field "viewRelation" value;

  # `readsOf` — the cells a view relation CONSUMED. One per surviving contribution: the walk
  # reached that scope and the fold read what it found there.
  #
  # ★ IT IS DEFINED ON THE MATERIALIZED RESULT AND NOT ON THE DEFINITION, and that is forced
  # rather than chosen: a definition names a root and an admission policy, never the membership
  # those resolve to. A `readsOf` over a definition would have to answer before the walk that
  # determines its own answer, which is why the shipped surface it replaces refuses an unresolved
  # membership by name instead of guessing one.
  readsOf =
    r:
    let
      v = materialized "readsOf" "relation" r;
    in
    unique (map (c: cell c.scope v.name "input") v.contributions);

  # `writesOf { relation; target; mode; }` — the cell a placed view relation PRODUCES.
  #
  #   merge at a root        → the root's OUTPUT cell. Nothing folds an output cell, so a merging
  #                            view is a SINK of the schedule.
  #   nest / nest-verbatim   → the target root's INPUT cell: the placed content joins that bucket,
  #                            which is what a collector rooted there reads.
  #   the terminal sink      → a position outside the graph entirely, which no view can read.
  #
  # ★ IT TAKES THE PLACEMENT AND NOT ONLY THE RELATION, and that is forced rather than chosen: WHICH
  # cell a result lands in is a placement fact, and placement is deliberately not a declaration
  # field. A `writesOf` that read the declaration alone would have to guess the mode, and the guess
  # is exactly the difference between a sink and a producer.
  writesOf =
    args:
    let
      a = fields "writesOf" [
        "relation"
        "target"
        "mode"
      ] args;
      v = materialized "writesOf" "relation" a.relation;
      target = elementOf "writesOf" "target" "target" a.target;
      mode = choice "writesOf" "mode" placement.modes a.mode;
    in
    if target.arm == "output" then
      [ ("out:" + builtins.concatStringsSep "." target.path + "@output") ]
    else if target.channel != v.name then
      # ★ THE CROSS-CHECK IS WHAT MAKES THE TYPE CHECK ABOVE LOAD-BEARING RATHER THAN DECORATIVE.
      # A root target carries its own channel, so a caller can name a cell this result does not
      # produce — and the schedule would then be built on an arc nobody has. Refusing the mismatch
      # also forces the materialized-result check, which a binding that were merely declared and
      # never read would leave unevaluated and therefore unrun.
      refuse "writesOf"
        "the target names channel '${target.channel}' but the view relation is named '${v.name}'; a result lands in the cell it is named for, and a target naming another cell would put the schedule's arc where nothing writes"
    else
      [ (cell target.scope target.channel (if mode == "merge" then "output" else "input")) ];

  # `unit { relation; target; mode; }` — a materialized view relation together with the placement
  # that decides which cell it produces. It is what the schedule's nodes are, because neither half
  # alone determines an arc.
  unit =
    args:
    let
      a = fields "unit" [
        "relation"
        "target"
        "mode"
      ] args;
    in
    {
      __element = "unit";
      relation = materialized "unit" "relation" a.relation;
      target = elementOf "unit" "target" "target" a.target;
      mode = choice "unit" "mode" placement.modes a.mode;
    };

  # `accumulatorRelation { relations }` — the dependency relation, as the node set plus the
  # accessor gen-graph's ordering surfaces read. `relations` is an ATTRSET of named view relations.
  # Edge direction follows that library's own convention: `edges u ∋ v` means "u DEPENDS ON v", so
  # an ordering is producers-first.
  #
  # ★★ THE SCHEDULE'S NODE KEY IS THE CALLER'S OWN BINDING NAME, NOT THE VIEW'S CHANNEL AND NOT THE
  # CELL IT WRITES — and that follows directly from the dropped output-independence condition. TWO
  # VIEWS MAY WRITE ONE CELL: that is the ordinary case here, not the pathological one. A key
  # derived from the cell could not tell those two apart, so the relation would either refuse a
  # lawful pair or silently merge them into one node. An attrset key is collision-free by
  # construction, so the schedule cannot be a claim about a node that is secretly two.
  accumulatorRelation =
    args:
    let
      a = fields "accumulatorRelation" [ "units" ] args;
      names = builtins.attrNames a.units;
      nodes = map (n: {
        name = n;
        unit = elementOf "accumulatorRelation" "units" "unit" a.units.${n};
      }) names;
      writes = map (n: {
        inherit (n) name;
        cells = writesOf {
          inherit (n.unit) relation target mode;
        };
      }) nodes;
      byName = builtins.listToAttrs (
        map (x: {
          inherit (x) name;
          value = x;
        }) nodes
      );
    in
    if !(builtins.isAttrs a.units) then
      refuse "accumulatorRelation" "field 'units' must be an attrset of named units; the attribute name is the schedule's node key, and it is the caller's because two units may lawfully write one cell"
    else
      {
        __element = "accumulatorRelation";
        inherit nodes;
        keyOf = n: n.name;
        # FLOW DEPENDENCE ONLY — output independence is dropped, per the relaxation above. A
        # co-writing pair is left unordered here on purpose.
        edges =
          n:
          let
            reads = readsOf n.unit.relation;
            depends = filter (w: w.name != n.name && (filter (c: elem c reads) w.cells) != [ ]) writes;
          in
          map (w: byName.${w.name}) depends;
      };

  # `accumulatorOrder { relations }` — the schedule, as the caller's names in producers-first
  # order. The SORTER is gen-graph's Kahn arm reached BY ITS OWN NAME rather than through the
  # selecting door: a caller whose correctness depends on which algorithm answered binds the named
  # arm, and this one does.
  accumulatorOrder =
    args:
    let
      rel = accumulatorRelation args;
      sorted = graph.topoOrderKahn {
        inherit (rel) nodes edges keyOf;
      };
    in
    if sorted.ok then
      map (n: n.name) sorted.order
    else
      # ★ A CYCLE HERE IS A REAL CONDITION AND IS NAMED RATHER THAN DENIED. The ordering door's
      # input type makes a query unable to decide whether an edge exists, so a single view cannot
      # depend on its own result — but two views CAN read where each other writes, and that is a
      # flow-dependence cycle with no producers-first order at all. The refusal reports WHICH
      # views, because the caller has already been handed a decomposition and re-deriving it by
      # hand is work the sorter has done.
      refuse "accumulatorOrder"
        "the flow-dependence relation has no producers-first order: ${
          builtins.toJSON (map (c: map (n: n.name) c) sorted.cycles)
        } read where each other writes";

  # `orderedFoldOf { relations; mode; path; }` — the door a consumer actually calls: schedule the
  # views, then hand back their results in producers-first order with their placements resolved. It
  # is the one entry point that composes the schedule with the placement family, and it takes the
  # materialized results for the reason stated at the top of this file.
  orderedFoldOf =
    args:
    let
      a = fields "orderedFoldOf" [
        "units"
        "path"
      ] args;
      order = accumulatorOrder { inherit (a) units; };
    in
    map (
      n:
      placement.place {
        inherit (a) path;
        inherit (a.units.${n}) mode;
        name = n;
        value = a.units.${n}.relation.value;
      }
    ) order;
in
{
  inherit
    cell
    unit
    readsOf
    writesOf
    accumulatorRelation
    accumulatorOrder
    orderedFoldOf
    materialized
    ;
}
