# THE VIEW RELATION — a view definition and a scope graph become THE NAMED RESULT.
#
# Manchanda & Warren, Minker 1988 ch. 10, printed 381, names both ends of this: the "view
# definition" is the declaration and the "view relation" is the result. The ACT between them has
# no term at any held primary and so has no identifier here — the two named things are enough, and
# inventing a third name for the arrow would be presenting an unacquired term as acquired.
#
# ── WHAT THE MATERIALIZATION DOES, IN ORDER ─────────────────────────────────────────────────
#  1. direction — a LABELLED transpose for the inbound arm. Transpose reverses direction rather
#     than erasing it; reaching the plain transpose through a label-forgetting projection would
#     erase precisely the component the walk reads.
#  2. effective E = NODE MARKS ∩ DECLARED ADMISSION. The marks are applied AT THE ACCESSOR, which
#     is where the calculus puts them, so the construction only ever REMOVES edges: WIDENING IS
#     NOT FORBIDDEN, IT IS UNSAYABLE — intersection has no inverse the author can reach, and there
#     is no global dial to disagree with the derivation because the mark IS an input to it.
#  3. the walk — a witness-carrying enumeration constrained by E, so `WFL ⊢ p ok` holds of every
#     answer by construction.
#  4. the projection — a MIN-FOLD OVER `distance` WITHIN EACH ⟨node, derivative-state⟩ CLASS.
#     ★ A CARRIER KEYED FINER THAN THE DECLARATION IS NOT A MISMATCH, because the projection is
#     part of the materialization and not a chore left to a consumer. The converse does not hold:
#     A DECLARATION MAY NEVER KEY FINER THAN ITS CARRIER, and cannot, since no projection can
#     un-merge what the carrier has already merged.
#  5. (NR-Rel) — at each surviving scope the relation is reached ONCE, AT THE END OF THE PATH,
#     and the datum is filtered by WFD. `data(G)` is a COMPONENT of the graph value, so what is
#     found there was authored before this materialization began: no step of the walk can put a
#     datum where a later step reads one, and a walk-emitted contribution is not a thing that can
#     exist rather than a thing that is filtered out.
#  6. competition — contributions are grouped by k and the surviving-maximal set of each group is
#     taken under the label order's lexicographic lift.
#  7. the tie-set disposition — `union`, `refuse` or `orderedFold`, named by the declaration.
#  8. dedup — declared, and EVERY DROP IS A RECORD.
#  9. the fold — ASSOCIATIVE-ONLY, WITH NO REORDER AND NO DEDUP BY RANK. The lawful shape states
#     it in its own words: "NOTHING IS SORTED, DEDUPED OR FILTERED BY RANK. The list's order IS
#     the authority." ★ A fold over the SORTED answer set requiring a commutative-idempotent
#     monoid is NOT a successor to this and must not be reached for — it is the exact
#     reorder-and-dedup this step forbids.
#
# ── WHAT IS DELIBERATELY NOT A DECLARATION FIELD ────────────────────────────────────────────
# Boundary marks belong to the NODE: a declaration CONSUMES marks and never sets, waives or names
# them, which is why they are an argument to this function and not a field of the definition. And
# placement, the terminal sink and content transformation are not fields either — folding those in
# would reconstruct the released edge grammar under new names. They live in their own construct
# families (`placement.nix`, `transform.nix`), reachable and separate.
{ prelude, graph }:
let
  inherit (prelude)
    concatMap
    elem
    filter
    foldl'
    head
    length
    map
    sort
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  inherit (refusal) refuse fields quote;
  inherit (carrierLib) elementOf;

  indexOf =
    xs: x:
    let
      n = length xs;
      go =
        i:
        if i >= n then
          null
        else if builtins.elemAt xs i == x then
          i
        else
          go (i + 1);
    in
    go 0;

  # `groupsInWalkOrder keyOf xs` — `builtins.groupBy` keyed by `keyOf`, with the GROUPS returned in
  # order of first appearance rather than in attribute-name order.
  #
  # ★ THE DISTINCTION IS THE WHOLE OF STEP 9's LAW SEEN ONE LEVEL UP. `attrNames` sorts
  # lexicographically, so concatenating groups by name would make the result's order a fact about
  # KEY SPELLING and not about the walk. Within a group the order is already the walk's; across
  # groups it has to be too, or the fold's "the list's order is the authority" is authority over
  # an order nobody chose.
  groupsInWalkOrder =
    keyOf: xs:
    let
      grouped = builtins.groupBy keyOf xs;
      seen = foldl' (
        acc: x:
        let
          k = keyOf x;
        in
        if elem k acc then acc else acc ++ [ k ]
      ) [ ] xs;
    in
    map (k: {
      key = k;
      members = grouped.${k};
    }) seen;

  viewRelation =
    args:
    let
      a = fields "viewRelation" [
        "definition"
        "graph"
        # REQUIRED, and "no marks" is `_: [ ]` written down. A defaulted mark accessor would make
        # the unmarked case a decision nobody made, on the one axis where silence must never read
        # as access.
        "marks"
      ] args;
      def = elementOf "viewRelation" "definition" "viewDefinition" a.definition;
      g = elementOf "viewRelation" "graph" "scopeGraph" a.graph;

      # 1 — direction.
      directed = if def.direction == "inbound" then graph.labeledTranspose g.labeled else g.labeled;

      # 2 — effective E. `boundedBy` removes edges AT THE ACCESSOR and reports what it removed;
      # the companion diagnostic is never empty where it fires, so silence and a boundary are
      # never the same reading.
      bounded = graph.boundedBy directed a.marks;

      # 3 — the walk. WFD does NOT run here: under (NR-Rel) the path is constrained by WFL and the
      # DATUM by WFD, and collapsing the two would filter scopes by a predicate written for data
      # terms. The walk's own predicate is therefore total.
      answers = graph.query {
        mode = "paths";
        graph = bounded;
        from = def.root;
        follow = def.admission.expr;
      };

      # Distance and residual derivative state, folded along each witness. The residual state is
      # the admission policy still in force at the arrival — the component the ⟨node,
      # derivative-state⟩ collapse is keyed on.
      measured = map (
        ans:
        let
          walked =
            foldl'
              (acc: step: {
                distance = def.distance {
                  inherit (acc) distance;
                  inherit (step) label from to;
                };
                state = def.admission.step step.label acc.state;
              })
              {
                distance = 0;
                state = def.admission.expr;
              }
              ans.path;
        in
        {
          inherit (ans) node path;
          inherit (walked) distance;
          admission = def.admission.stateKey walked.state;
        }
      ) answers;

      # 4 — the projection. Min over `distance` within each ⟨node, derivative-state⟩ class; a tie
      # in distance keeps the first arrival in walk order, because the walk's order is the only
      # order this step has any business pinning.
      projected =
        map
          (
            cls:
            let
              best = foldl' (acc: m: if m.distance < acc.distance then m else acc) (head cls.members) (
                builtins.tail cls.members
              );
            in
            best
          )
          (
            groupsInWalkOrder (
              m:
              builtins.toJSON [
                m.node
                m.admission
              ]
            ) measured
          );

      # 5 — (NR-Rel), over the WALK-INDEPENDENT data component.
      contributions = concatMap (
        m:
        map (datum: {
          scope = m.node;
          inherit (m) distance path admission;
          inherit (def) relation;
          inherit datum;
          channel = def.name;
        }) (relationAt m.node)
      ) projected;

      # ★★★ THE LOOKUP IS THE PUBLISHED `relationLookup`, NOT A PRIVATE TWIN OF IT — and that is
      # the whole of the fix, because the twin was identical BUT FOR THE REFUSAL. Reaching the data
      # component inline dropped (NR-Rel)'s undeclared-relation check, so a misspelled relation and
      # a declared relation with no datums both answered `[ ]`, indistinguishable in the result.
      # That is the exact failure this library's refusal discipline exists to forbid, reproduced by
      # the library against itself.
      #
      # ★★ IT IS ALSO THE RAW-LAYER DISCIPLINE HOLDING AGAINST ITS OWN AUTHOR: a materialization
      # that reached past a published element into a private near-copy would leave that element a
      # second surface nobody runs, and the calculus hidden behind the composition again.
      #
      # ★★ THERE IS NOTHING HERE ABOUT *WHICH* READING OF THE DATA COMPONENT TO TAKE, BECAUSE THERE
      # IS ONLY ONE. `data` is a component of the graph value, so the datums at a scope are fixed
      # before this materialization begins and no step of it can add one. The discriminator that
      # used to sit at this line — severing the scope's out-edges to find the walk-independent
      # reading — is gone with the divergence that made two readings possible.
      relationAt =
        scope:
        carrierLib.relationLookup {
          graph = g;
          inherit scope;
          inherit (def) relation wellFormed;
        };

      # 6 — competition, over a STRICT PARTIAL ORDER.
      #
      # ★★★ "NOT BEATEN BY THE MINIMUM" IS WRONG HERE AND THE PROSE THAT CLAIMED IT WAS THE TELL.
      # Struck, quoted so it is not re-introduced: ~~*"the lift is a TOTAL PREORDER on rank words …
      # so minimal reduces to not beaten by the minimum"*~~. Fig. 1's `<l` is a strict PARTIAL
      # order, its lift `<p` is partial too, and a faithful lift of a partial order cannot be
      # total. Under a partial order a group has an ANTICHAIN of minimal elements, and picking one
      # of them as "the minimum" silently shadows everything the others leave visible.
      #
      # THE SURVIVING-MAXIMAL SET IS THEREFORE COMPUTED AS MINIMALITY: a contribution survives iff
      # NOTHING in its group strictly precedes it.
      #
      # ★★ THE SCAN IS BOUNDED WITHOUT WEAKENING THAT. `rankLess` is a TOTAL order on rank words
      # that `<p` refines — `a <p b` implies `rankLess a b`, because the first position where two
      # rank words differ can only be a position where the LABELS differ, and `<p` decides exactly
      # there. So sorting by it puts every dominator ahead of everything it dominates, and each
      # candidate need only be compared against the SURVIVORS KEPT SO FAR: `<p` is transitive, so a
      # candidate dropped by an already-dropped element was dropped by whatever dropped that one.
      # The cost is Θ(n log n) plus the antichain's width, which is 1 wherever the order is total —
      # the ordinary case — against Θ(n²) for the pairwise definition.
      # `ci/tests/relation.nix` runs both forms against each other on the same fixtures.
      competed = map (
        grp:
        let
          byRank = sort (x: y: def.order.rankLess x.path y.path) grp.members;
          kept = foldl' (
            acc: c: if builtins.any (o: def.order.pathPrecedes o.path c.path) acc then acc else acc ++ [ c ]
          ) [ ] byRank;
          # Emitted in WALK order, never in the sort key's: the sort is a bound on the computation
          # and has no business pinning the answer's order.
          survives = c: elem c kept;
        in
        {
          inherit (grp) key;
          visible = filter survives grp.members;
          shadowed = filter (c: !(survives c)) grp.members;
        }
      ) (groupsInWalkOrder (c: def.channel.keyOf c) contributions);

      # 7 — the tie-set disposition.
      disposed = map (
        grp:
        if def.tieSet.arm == "union" then
          # The papers' own arm: the surviving-maximal set IS the answer, in walk order.
          grp
        else if def.tieSet.arm == "refuse" then
          (
            if length grp.visible > 1 then
              refuse "viewRelation" "channel '${def.name}' declares tieSet 'refuse' and the competition key ${builtins.toJSON grp.key} survives with ${toString (length grp.visible)} contributions, from scopes ${
                quote (map (c: c.scope) grp.visible)
              }; the declaration asked for exactly one"
            else
              grp
          )
        else
          # orderedFold — the surviving set is disposed by the DECLARED contribution order over
          # the contributing scopes. A list is invariant under presentation order by construction,
          # where a comparator over arrival position is not; and the order is TOTAL over the
          # survivors, so a scope it does not name is refused by name rather than sorted to an end
          # nobody declared.
          let
            unranked = filter (c: indexOf def.tieSet.order c.scope == null) grp.visible;
          in
          if unranked != [ ] then
            refuse "viewRelation" "channel '${def.name}' declares tieSet 'orderedFold' whose declared order (${quote def.tieSet.order}) does not rank the contributing scope '${(head unranked).scope}'; the order is total over the surviving set"
          else
            grp
            // {
              visible = sort (
                x: y: indexOf def.tieSet.order x.scope < indexOf def.tieSet.order y.scope
              ) grp.visible;
            }
      ) competed;

      surviving = concatMap (grp: grp.visible) disposed;
      shadowed = concatMap (grp: grp.shadowed) disposed;

      # 8 — dedup, with EVERY DROP A RECORD. The surface this replaces declared a dedup and
      # enumerated no drops, so an answer that came back short could not be told from a
      # contribution that was never made.
      dedupKey =
        c:
        if def.dedup.arm == "byDatum" then
          builtins.toJSON c.datum
        else if def.dedup.arm == "byKey" then
          def.dedup.keyOf c
        else
          null;
      deduped =
        if def.dedup.arm == "none" then
          {
            kept = surviving;
            dropped = [ ];
          }
        else
          # The index is an ATTRSET rather than a rescan of what has been kept. A rescan pays the
          # kept list once per contribution, which is quadratic in the group's size on the one
          # step whose whole purpose is to make a large gather smaller.
          foldl'
            (
              acc: c:
              let
                k = dedupKey c;
                idx = builtins.toJSON k;
              in
              if acc.seen ? ${idx} then
                acc
                // {
                  dropped = acc.dropped ++ [
                    {
                      contribution = c;
                      collapsedInto = acc.seen.${idx};
                      policy = def.dedup.arm;
                      key = k;
                    }
                  ];
                }
              else
                acc
                // {
                  kept = acc.kept ++ [ c ];
                  seen = acc.seen // {
                    ${idx} = c;
                  };
                }
            )
            {
              kept = [ ];
              dropped = [ ];
              seen = { };
            }
            surviving;

      # 9 — the fold. `foldl'` over the list AS IT STANDS: no sort, no dedup by rank, no reorder.
      value = foldl' def.combine.op def.empty (map (c: c.datum) deduped.kept);

      # The boundary diagnostic, MATERIALIZED AS DATA AND CARRIED INSIDE THE RESULT. A side channel
      # a consumer may ignore is exactly the fail-open shape that "boundary as a query property the
      # query may omit" was refused for; silence must not become access at the diagnostic either.
      withheld = concatMap (
        scope:
        map (w: {
          inherit scope;
          inherit (w) label target marks;
        }) (bounded.withheld scope)
      ) g.scopes;
    in
    {
      __element = "viewRelation";
      name = def.name;
      definition = def;
      graph = g;
      inherit value shadowed withheld;
      contributions = deduped.kept;
      inherit (deduped) dropped;
    };
in
{
  inherit viewRelation groupsInWalkOrder indexOf;
}
