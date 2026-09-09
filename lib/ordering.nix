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
#
# ── A SECOND DOOR, A DIFFERENT INPUT-TYPE LAW ────────────────────────────────────────────────
# `boundedWellDefinedSchedule` (ADR-0008 §3) is not this door and does not owe it the law above.
# Its input type is `gen-graph.mkDeclaredEdges`'s contracted declared relation, and that relation
# obtains its guarantee at CONSTRUCTION — `deepSeq`-forced there, so a relation closing back over
# the evaluation it orders diverges before this library ever reads it — never by materialization.
# The two doors share nothing but the file: one refuses a raw labelled-edge accessor because a
# query's answer cannot decide whether an edge exists, the other admits a value already forced
# closed at its own construction site.
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
  inherit (refusal)
    refuse
    fields
    choice
    strings
    quote
    ;
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

  # `boundedWellDefinedSchedule { nodes; declaredDependencies; equations; admitsCycle; }` — ADR-0008
  # §3's static well-definedness gate, re-homed as a query over gen-graph's CONTRACTED declared
  # relation (owner-ruled 2026-09-09). It is Vogt's `bounded well-defined` (Definition 3.14), NOT
  # `well defined`. Theorem 3.2 carries THREE conjuncts — completeness, no cycle under EDDP, and a
  # once-per-path non-terminal bound; ADR-0008 §3 rules the gate takes the first two and omits
  # finiteness. ★ THIS CONSTRUCT COMPUTES THE SECOND CONJUNCT ONLY. `equations` is accepted,
  # required and returned unread — so a caller can pair the schedule with the equations it was built
  # from — but no field of it is read HERE, so completeness (every attribute of every symbol is
  # effectively computable) is neither checked nor assumed by this code. Whether it holds by
  # construction elsewhere in gen, or is owed to a later construct, is not decided in this file; a
  # caller relying on it must find that ground independently. AT VOGT'S OWN STATED PRICE FOR
  # OMITTING FINITENESS: "Finite expansion of the structure tree, however, is no longer
  # guaranteed." A REFUSAL DOES NOT IMPLY ILL-DEFINEDNESS: well-definedness ⟸ absence of a declared
  # cycle (Knuth 1968, MST 2(2) 127-145, cited for the reduction and for that one direction only),
  # never ⟺. The 1971 correction (MST 5(1) 95-96) repaired Knuth's per-symbol §3 ALGORITHM — a set
  # of graphs per symbol, tested for an oriented cycle — which this construct does NOT implement:
  # gen has no productions, this condenses ONE declared graph, and the 1971 obligation is therefore
  # not in force here; it is cited as the negative that keeps this construct from claiming the test.
  #
  # `declaredDependencies` is the contracted value `gen-graph.mkDeclaredEdges` returns — admitted by
  # NAME and refused BY NAME, nominal and not structural: a hand-assembled attrset carrying an
  # `index` and a `dependencies` has the right shape and is precisely the bypass. The type is
  # `gen-graph`'s and the refusal is this library's, per `require-declared-dependencies.nix`'s own
  # convention for the same contract. `nodes` is the registration set — a formal because the
  # constructor's own index is grouped by source and omits sinks, and because this library holds no
  # evaluator and must not acquire one. ★ `nodes` MUST CONTAIN EVERY ENDPOINT OF THE DECLARED
  # RELATION IT IS HANDED, and this is CHECKED rather than assumed: an endpoint outside `nodes`
  # either narrows the partition silently (a cyclic component built from only the seen half is
  # admitted) or reaches gen-graph's own partitioner for a node it never registered, which aborts
  # uncatchably. Both regimes are refused BY NAME here, from the contracted value alone — `index`'s
  # keys are the relation's sources, its values the targets — no evaluator, no second construction.
  # `admitsCycle` is the carve-out authority (Sloane 2009 iterate-to-fixpoint is its ground) —
  # REQUIRED AND TOTAL, no default, because a default is a decision nobody made and nobody can see —
  # and it is `id -> bool`, `mkNodeRef`'s own shape: the membership authority arrives as a parameter
  # about a registered substrate this library does not hold. A value that is not a function is
  # refused by name at the door. `builtins.isFunction` narrows the class but does not CLOSE it —
  # Nix has no reliable arity predicate, so a wrong-arity or wrong-return-type `admitsCycle` still
  # satisfies it and would otherwise reach `builtins.all` and abort uncatchably. `den-hoag-g8lo`'s
  # SHIPPED predicate — its landed state, not the orchestrator's round-4 ruling this header used to
  # quote, which the bead's own record retires as wrong in its specifics — is
  # `isFunction v || (isAttrs v && v ? __functor)`. THIS DOOR IS DELIBERATELY NARROWER, lambda-only:
  # the contracted shape here is `mkNodeRef`'s own, a lambda, and a `__functor` callable is refused
  # BY NAME rather than admitted. `admits` below checks the APPLIED RESULT, not the function's
  # shape: forcing `a.admitsCycle n` to a bool CLOSES UNDER-APPLICATION (a curried `_: _: true`
  # forces to a lambda, not a bool, at the same site) and WRONG RETURN TYPE. It does NOT close a
  # PATTERN FORMAL (`{ x }: true` or `{ x, ... }: true`) — such a value still satisfies
  # `isFunction`, and applying it to a string node identifier aborts UNCATCHABLY while `r` is
  # computed, before `admits`'s own check ever runs, escaping `builtins.tryEval` in the same way.
  # No check on `r` can see a failure that happens computing `r`; that residue is pinned as a
  # falsifier cell in `ci/tests-error.nix` rather than closed here.
  boundedWellDefinedSchedule =
    args:
    let
      a = fields "boundedWellDefinedSchedule" [
        "nodes"
        "declaredDependencies"
        "equations"
        "admitsCycle"
      ] args;
      nodes = strings "boundedWellDefinedSchedule" "nodes" a.nodes;
      declaredDependencies =
        if graph.isDeclaredEdges a.declaredDependencies then
          a.declaredDependencies
        else if builtins.isAttrs a.declaredDependencies then
          refuse "boundedWellDefinedSchedule" "field 'declaredDependencies' must be the relation `gen-graph.mkDeclaredEdges` returns; received an attrset that `mkDeclaredEdges` did not build"
        else
          refuse "boundedWellDefinedSchedule" "field 'declaredDependencies' must be the relation `gen-graph.mkDeclaredEdges` returns; received a ${builtins.typeOf a.declaredDependencies}";
      # Containment, decided from the contracted value alone: `index`'s keys are the sources,
      # its values the targets. No evaluator, no second construction — see the header above.
      sources = builtins.attrNames declaredDependencies.index;
      targets = builtins.concatLists (builtins.attrValues declaredDependencies.index);
      missingEndpoints = unique (filter (e: !(elem e nodes)) (sources ++ targets));
      edges = declaredDependencies.dependencies;
      condensation = graph.condensation { inherit nodes edges; };
      selfLoop = n: elem n (edges n);
      isCyclicScc =
        scc: (builtins.length scc > 1) || (builtins.length scc == 1 && selfLoop (builtins.head scc));
      # The applied-result check: forcing `a.admitsCycle n` to a bool closes under-application and
      # wrong return type — see the header above; a pattern formal still aborts uncatchably inside
      # this binding, before this check runs. `a.admitsCycle` is already known to be a function
      # here, because this binding is only ever forced after the `isFunction` refusal above has
      # passed.
      admits =
        n:
        let
          r = a.admitsCycle n;
        in
        if builtins.isBool r then
          r
        else
          refuse "boundedWellDefinedSchedule" "field 'admitsCycle' must return a bool for every node identifier; for `${n}` it returned a ${builtins.typeOf r}";
      # `builtins.all` SHORT-CIRCUITS at the first `false`: an ill-typed member of the same cyclic
      # component that sits after a genuinely-false one is never forced, so the raised refusal is
      # the (true, named, catchable) cycle refusal below rather than this type refusal, and the
      # message will not name the ill-typed member.
      badSccs = filter (scc: isCyclicScc scc && !(builtins.all admits scc)) condensation.sccs;
    in
    if missingEndpoints != [ ] then
      refuse "boundedWellDefinedSchedule" "field 'nodes' does not contain the declared relation's endpoint(s) ${quote missingEndpoints}; ADR-0008 §3's precondition is a declared edge set complete at registration, so every source and target `declaredDependencies` names must be a member of `nodes`"
    else if !(builtins.isFunction a.admitsCycle) then
      refuse "boundedWellDefinedSchedule" "field 'admitsCycle' must be a function from a node identifier to a bool (`mkNodeRef`'s own shape); received a ${builtins.typeOf a.admitsCycle}"
    else if badSccs != [ ] then
      refuse "boundedWellDefinedSchedule" "the declared relation has a cyclic component `admitsCycle` does not admit: ${builtins.toJSON badSccs}. Declare `admitsCycle` true for every member (Sloane 2009 iterate-to-fixpoint) or break the cycle; this refusal is not a well-definedness verdict (well-definedness ⟸ absence of a declared cycle, never ⟺)"
    else
      {
        inherit (a) equations;
        inherit condensation edges;
      };
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
    boundedWellDefinedSchedule
    ;
}
