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
#     taken under the EFFECTIVE order's lexicographic lift: the lexicographic product of the
#     declared ORDER MARK with the declaration's own order, MARK OUTER. An all-tied mark is the
#     identity, so a declaration that marks nothing competes exactly as it did before.
#  7. the tie-set disposition — `union`, `refuse` or `orderedFold`, named by the declaration.
#  8. dedup — declared, and EVERY DROP IS A RECORD.
#  9. the fold — ASSOCIATIVE-ONLY, WITH NO REORDER AND NO DEDUP BY RANK. The lawful shape states
#     it in its own words: "NOTHING IS SORTED, DEDUPED OR FILTERED BY RANK. The list's order IS
#     the authority." ★ A fold over the SORTED answer set requiring a commutative-idempotent
#     monoid is NOT a successor to this and must not be reached for — it is the exact
#     reorder-and-dedup this step forbids. The fold is bracketed as a BALANCED TREE under the arm's
#     declared associativity (`foldCombine`); the list's order is still the authority, and nothing
#     is sorted, deduped or reordered.
#
# ── WHAT IS DELIBERATELY NOT A DECLARATION FIELD ────────────────────────────────────────────
# Boundary marks belong to the NODE: a declaration CONSUMES marks and never sets, waives or names
# them, which is why they are an argument to this function and not a field of the definition. And
# placement, the terminal sink and content transformation are not fields either — folding those in
# would reconstruct the released edge grammar under new names. They live in their own construct
# families (`placement.nix`, `transform.nix`), reachable and separate.
#
# ★★★ THE ORDER MARK IS THE SAME ARGUMENT-NOT-A-FIELD FOR THE SAME REASON, and the reason is the
# whole of what it buys. An order mark declared INSIDE the definition would be a mark the query
# SETS, and a query that sets its own mark can set the identity and decline — which is precisely
# the state a mandate has to be able to bind out of. `def.order` is untouched by this: every
# declaration written before the mark existed means exactly what it meant.
{ prelude, graph }:
let
  inherit (prelude)
    concatMap
    filter
    foldl'
    head
    length
    map
    sort
    unique
    ;
  enums = import ./enumerations.nix { inherit prelude; };
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  inherit (refusal)
    refuse
    fields
    decided
    returned
    formalsOf
    quote
    renderSubject
    renderValue
    sortNames
    ;
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
  #
  # The order is walk-FIRST appearance because gen-prelude's `unique` builds a key→first-index
  # table with `listToAttrs`, which keeps the FIRST binding of a repeated name, and emits the keys
  # by ascending index — linear in list elements where an `acc ++ [ k ]` fold is quadratic.
  groupsInWalkOrder =
    keyOf: xs:
    let
      grouped = builtins.groupBy keyOf xs;
    in
    map (k: {
      key = k;
      members = grouped.${k};
    }) (unique (map keyOf xs));

  # `bucketAddress x` — step 8's bucket address: `toJSON` over `x` with every LAMBDA replaced by
  # one constant tag. The tag is an ADDRESS, not ADR-0034's type-tagged encoding and not a mint:
  # it selects a bucket and never decides; `same`, Nix `==`, decides. All it owes is to coarsen
  # `==` (`a == b` implies equal addresses), which one tag for every lambda does. ADR-0034's
  # "until it does, that component's collapse is replaced by a refusal rather than by a
  # structural identity" does not reach here: what it refuses is an IDENTITY, and this address
  # mints none (it is also why nothing here is refused: nothing demands an identity).
  # A function-free value addresses byte-identically to `toJSON`. `__toString` is left whole
  # because `toJSON` CALLS it; `outPath` needs no case, because `mapAttrs` is lazy and `toJSON`
  # reads only `outPath` from the tagged set — so a derivation, which refers to itself, is never
  # walked.
  bucketAddress =
    x:
    let
      tag =
        v:
        if builtins.isFunction v then
          { __lambda = null; }
        else if builtins.isList v then
          map tag v
        else if builtins.isAttrs v then
          if v ? __toString then v else builtins.mapAttrs (_: tag) v
        else
          v;
    in
    builtins.toJSON (tag x);

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
        # REQUIRED on the same terms, and "no order mark" is the one-layer order over L̂ written
        # down. A defaulted identity would make the unmarked competition a decision nobody made on
        # the one axis that decides who wins, and `labelOrder` already refuses an unranked letter
        # for the same reason: a rank nobody declared is not a rank.
        "orderMark"
      ] args;
      def = elementOf "viewRelation" "definition" "viewDefinition" a.definition;
      g = elementOf "viewRelation" "graph" "scopeGraph" a.graph;
      markOrder = elementOf "viewRelation" "orderMark" "labelOrder" a.orderMark;

      # 1 — direction.
      directed = if def.direction == "inbound" then graph.labeledTranspose g.labeled else g.labeled;

      # 2 — effective E. `boundedBy` removes edges AT THE ACCESSOR and reports what it removed;
      # the companion diagnostic is never empty where it fires, so silence and a boundary are
      # never the same reading.
      #
      # The accessor's RESULT is checked where gen-graph consumes it: a list, of marks carrying a
      # `name` and a callable `admits`, and each `admits` verdict a bool. Only that shape is forced;
      # a mark's `name` is carried unforced into `withheld`.
      bounded = graph.boundedBy directed marksAt;
      marksAt =
        s:
        map (markAt s) (
          returned "viewRelation" "field 'marks' at scope ${renderSubject s}"
            "it must return the list of boundary marks `{ name; admits; }` at that scope"
            builtins.isList
            (a.marks s)
        );
      callable =
        v:
        builtins.isFunction v || (builtins.isAttrs v && v ? __functor && builtins.isFunction v.__functor);
      markAt =
        s: m:
        if !(builtins.isAttrs m && m ? name && m ? admits) then
          refuse "viewRelation" "field 'marks' at scope ${renderSubject s} returned a mark that is ${renderValue m}${
            if builtins.isAttrs m then " (fields: ${quote (builtins.attrNames m)})" else ""
          }; a mark is `{ name; admits; }`, and `withheld` reports it by its name"
        else if !(callable m.admits) || formalsOf m.admits != [ ] then
          refuse "viewRelation" "field 'marks' at scope ${renderSubject s} returned a mark whose 'admits' is ${renderValue m.admits}${
            if formalsOf m.admits != [ ] then
              " destructuring an attrset (formals: ${quote (formalsOf m.admits)})"
            else
              ""
          }; it is applied to a label, a string, so it must be a predicate taking one"
        else
          m
          // {
            admits =
              l:
              returned "viewRelation"
                "a mark's 'admits' at scope ${renderSubject s} for the label ${renderSubject l}"
                "it is a predicate on labels and must return a bool"
                builtins.isBool
                (m.admits l);
          };

      # 3 — the walk. WFD does NOT run here: under (NR-Rel) the path is constrained by WFL and the
      # DATUM by WFD, and collapsing the two would filter scopes by a predicate written for data
      # terms. The walk's own predicate is therefore total.
      answers = graph.query {
        mode = "paths";
        graph = bounded;
        from = def.root;
        follow = def.admission.expr;
      };

      # The distance rule's declared contract is `{ distance; from; label; to; } → int`
      # (`viewDefinition`), and step 4's `<`, `trace`'s order and `hashTrace` all read what it
      # returns. A non-int is refused by name where it enters, so those comparators never see an
      # operand outside their domain; the check is a thunk in the fold and fires only where the
      # distance is read. A string used to be accepted and compared lexicographically ("10" < "9").
      distanceOf =
        step: d:
        if builtins.isInt d then
          d
        else
          refuse "viewRelation" "channel ${renderSubject def.name} declares a distance rule that returned ${renderValue d} for the step ${renderSubject step.label} from ${renderSubject step.from} to ${renderSubject step.to}; the rule is `{ distance; from; label; to; } → int`, and the projection compares the distances it returns";

      # Distance and residual derivative state, folded along each witness. The residual state is
      # the admission policy still in force at the arrival — the component the ⟨node,
      # derivative-state⟩ collapse is keyed on. The walk steps gen-graph's kernel directly, as
      # `graph.query` does, never the element's `step` or `stateKey` (den-hoag-l83dk).
      measured = map (
        ans:
        let
          walked =
            foldl'
              (acc: step: {
                distance = distanceOf step (
                  def.distance {
                    inherit (acc) distance;
                    inherit (step) label from to;
                  }
                );
                state = graph.regex.deriv step.label acc.state;
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
          admission = graph.regex.stateKey walked.state;
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

      # 5 — (NR-Rel), over the WALK-INDEPENDENT data component. Reached through `relationEntries`,
      # not the datum-only `relationLookup`, so each contribution carries the component ENTRY'S
      # authored `ordinal` beside its `datum` — `element` is the declaration COORDINATE this entry
      # was read off, fixed at the component and never at the walk: the (a1) precision rider that
      # element identity is `(producer, ordinal)`, never the pair `(l, X)`, and that path-multiplicity
      # never enters it.
      contributions = concatMap (
        m:
        map (entry: {
          scope = m.node;
          inherit (m) distance path admission;
          inherit (def) relation;
          datum = entry.datum;
          channel = def.name;
          element = {
            producer = m.node;
            inherit (entry) ordinal;
          };
        }) (relationAt m.node)
      ) projected;

      # ★★★ THE LOOKUP IS THE PUBLISHED `relationEntries`, NOT A PRIVATE TWIN OF IT — and that is
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
        carrierLib.relationEntries {
          graph = g;
          inherit scope;
          inherit (def) relation wellFormed;
        };

      # ── THE EFFECTIVE ORDER — the LEXICOGRAPHIC PRODUCT of the mark with the declared order,
      # MARK OUTER ────────────────────────────────────────────────────────────────────────────────
      #   `a <ₑ b  ⟺  a <ₘ b  ∨  (a ≃ₘ b ∧ a <q b)`
      # The query may only refine INSIDE the mark's ties. It can never erase or reverse a pair the
      # mark declares, and an all-tied mark is the identity, under which `<ₑ` is `<q` exactly.
      #
      # ★★ IT IS PER QUERY ROOT, NOT PER NODE, BY CONSTRUCTION AND NOT BY CHOICE. `E` is consumed
      # per STEP, which is what lets its marks be per node. `<` is consumed ONCE PER COMPETITION
      # GROUP, and a group spans scopes — so per-node order marks composed along each arrival path
      # would compare members of ONE group under SEVERAL relations, under which transitivity is not
      # even statable. There is exactly one order per competition, hence one per root.
      #
      # ★★★ AND IT FLATTENS BACK ONTO THE SHIPPED CARRIER rather than putting a pair-keyed
      # comparator at step 6. The composite key of `l` is the pair `(rankₘ l, rank_q l)` under the
      # lex order on pairs; lex on pairs is TOTAL, so the induced relation is a strict WEAK order
      # and the distinct pairs number consecutively with equal pairs sharing a rank. What step 6
      # reads is therefore one ordinary `labelOrder` — `rankOf` and `pathPrecedes` are untouched,
      # and step 6's prefix minimum reads it unchanged. THE PAIR IS AN INTERMEDIATE
      # OF THE COMPOSITION AND NEVER A DURABLE SECOND NUMBER LINE: nothing downstream of the
      # flattening ever sees it.
      #
      # ★ Intersection was the literal transfer and it is NOT what this is. `<ₘ ∩ <q` leaves the
      # carrier — a weak order's incomparability is an equivalence and that class is not closed
      # under ∩ — and it is the FAIL-OPEN direction here, because the composition rule is
      # minimality and removing pairs ENLARGES the antichain. A mark composed by ∩ would be
      # powerless rather than binding.
      effectiveOrder =
        let
          q = def.order;
          # `rankOf` answers for `$` as well as for every letter, so ONE function covers L̂.
          keyOf = l: [
            (markOrder.rankOf l)
            (q.rankOf l)
          ];
          lexLess =
            x: y:
            let
              x0 = builtins.elemAt x 0;
              y0 = builtins.elemAt y 0;
            in
            x0 < y0 || (x0 == y0 && builtins.elemAt x 1 < builtins.elemAt y 1);
          distinct = foldl' (acc: k: if builtins.any (seen: seen == k) acc then acc else acc ++ [ k ]) [ ] (
            map keyOf q.alphabet.extended
          );
          ranked = sort lexLess distinct;
          # A layer MAY BE EMPTY, and that is the representation doing its job rather than failing
          # at it: where `$` holds a composite rank no letter shares, the empty layer is how a rank
          # belonging to `$` alone gets written down in a declaration made of letters.
          layers = map (k: filter (l: keyOf l == k) q.alphabet.letters) ranked;
          # L IS A SET — `edgeLabels` refuses a duplicate letter and nothing in this library gives
          # the list an ordering meaning — so the seam below compares the alphabets SORTED. The
          # rendering already is: `quote` sorts, so a raw-order predicate could print two identical
          # lists and claim they differ, which is a diagnostic saying nothing in the shape of one.
          # A forged alphabet carrying a non-string stays unsorted, and a lambda equals no letter,
          # so the seam refuses it by name rather than aborting in the sort.
          asSet = sortNames;
          # `lexLess` is `<` on ints. `labelOrder` mints int ranks from layer indices, so a genuine
          # element cannot fail this, but an element tag is a claim and not proof: a `//` on a
          # genuine order keeps the tag and replaces `rankOf`. Every rank of L̂ is checked before
          # the sort reads any, so a forged rank is refused by name rather than aborting in `<`.
          ranksOf =
            which: o:
            map (l: {
              inherit which l;
              rank = o.rankOf l;
            }) q.alphabet.extended;
          nonIntRanks = filter (x: !(builtins.isInt x.rank)) (
            ranksOf "orderMark" markOrder ++ ranksOf "the definition's order" q
          );
        in
        if asSet q.alphabet.letters != asSet g.carrier.labels.letters then
          # ★★★ THE OTHER HALF OF THE SAME SEAM — THE DECLARATION AGAINST THE GRAPH IT IS COMPOSED
          # WITH. The check below compares the ORDER MARK against the definition; this one compares
          # the DEFINITION against the graph's carrier, and neither implies the other. Both
          # intra-object checks still have nothing to say about it: `viewDefinition` compares a
          # definition's OWN admission against its OWN order and `carrier` a carrier's OWN members
          # against its OWN labels, so a definition wholly over one alphabet and a graph wholly over
          # a disjoint one are each internally consistent and, measured at the rev before this
          # arrived, CONSTRUCTED AND ANSWERED SILENTLY.
          #
          # ★★ AND THE ANSWER IT GAVE IS THE WORST SHAPE AVAILABLE: not an error one layer down but
          # a PLAUSIBLE SHORT ANSWER. `labelWellFormedness` refuses a literal outside its own
          # alphabet, so a foreign admission expression is well-formed over letters the graph does
          # not carry and matches NO edge of it — the walk therefore reaches the root and nothing
          # else, and the materialization returns the root's own datum as though that were the
          # gather. A composition over the wrong graph is indistinguishable from one whose query
          # legitimately found only the root.
          refuse "viewRelation"
            "the definition's alphabet is not the graph's (${quote q.alphabet.letters} vs ${quote g.carrier.labels.letters}); one composition has one L"
        else if markOrder.alphabet.letters != q.alphabet.letters then
          # ★★★ THE SEAM'S OWN REFUSAL, AND IT IS NOT INHERITED FROM ANYWHERE. The two checks that
          # look like they cover this are both INTRA-OBJECT: `viewDefinition` compares a
          # definition's OWN admission against its OWN order, and `carrier` compares a carrier's
          # OWN members against its OWN labels. THIS is where an order authored elsewhere MEETS the
          # declaration's order, and measured at the rev this arrived in, nothing looked across the
          # seam — a definition over one alphabet composed with a graph over a disjoint one
          # CONSTRUCTED AND ANSWERED SILENTLY while both of those checks fired as controls beside
          # it. `carrier`'s "one carrier has one L" is the PATTERN this follows; it was never the
          # enforcer that covered it. Without this, the product is taken over pairs in which one
          # component ranks letters the other has never heard of.
          refuse "viewRelation"
            "orderMark is built over a different alphabet than the definition's `order` (${quote markOrder.alphabet.letters} vs ${quote q.alphabet.letters}); one competition has one L"
        else if nonIntRanks != [ ] then
          refuse "viewRelation" "${(head nonIntRanks).which} ranks ${renderSubject (head nonIntRanks).l} at ${renderValue (head nonIntRanks).rank}; a label order ranks every symbol of L̂ by an int, and the competition compares the ranks"
        else
          carrierLib.labelOrder {
            inherit (q) alphabet;
            inherit layers;
            endOfPath = indexOf ranked (keyOf "$");
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
      # ★★ MINIMALITY IS A PREFIX MINIMUM OVER LABEL WORDS, AND THAT IS WHAT IS COMPUTED. Write
      # `ŵ = w·$` for a member's label word. `$` occurs only last and `edgeLabels` refuses it as a
      # letter, so the ŵ are prefix-free: two distinct ones first differ at a position `i` inside
      # both, below a shared prefix `u`, and `pathPrecedes` decides `a <p b` exactly there, by
      # `rankOf â[i] < rankOf b̂[i]`. So `c` is minimal iff at EVERY node `u = ĉ[0..i)` of its word
      # the symbol `ĉ[i]` has the minimum rank among the symbols the group's members take at `u`.
      # Not minimal ⇒ dropped: a `d <p c` diverges from `c` at some `i`, so `d` is at `ĉ[0..i)`
      # with a lower-ranked symbol and `c` misses that node's minimum. Dropped ⇒ not minimal: a `d`
      # at `ĉ[0..i)` whose symbol ranks below `ĉ[i]` takes a DIFFERENT symbol — `rankOf` is a
      # function, so unequal ranks are unequal symbols — hence `i` is their first divergence and
      # `d <p c`. The minimum is taken over every member at the node, dominated ones included,
      # because minimality quantifies over the whole group.
      #
      # ★★ THE NODE IS THE LABEL PREFIX, NEVER THE RANK PREFIX. Two DISTINCT labels of ONE rank
      # both attain the minimum at their shared node and then split into DIFFERENT children, where
      # they are never compared again — Fig. 1's prefix order only orders paths that share a
      # prefix. A node keyed by ranks would merge those children, and a third path extending one
      # of them would shadow the other: that drops a genuine survivor
      # (`test-a-rank-tie-between-distinct-labels-does-not-share-survival` pins it). The address is
      # `toJSON` of a list of letters, injective on lists of strings, so two members share a node
      # iff their label prefixes are `==`; survival is still decided by `<` on ranks, never by the
      # address.
      #
      # The cost is Θ(Σ ℓ²) over the group's members, ℓ a member's path length (each prefix address
      # is rebuilt), so it is linear in the number of members, scopes and distinct words; nothing
      # is sorted and no member is scanned against the survivors. `ci/tests/relation.nix` checks it
      # against the pairwise definition over the published `pathPrecedes`.
      #
      # ★ THE `seq` IS BOTH ALPHABET REFUSALS' ONLY REACH INTO THE EMPTY CASE, and it is here rather
      # than at the binding because `map` over NO groups would never force the order at all — a
      # cross-alphabet mark, or a definition composed with a foreign graph, on a query that happens
      # to gather nothing would then answer `[ ]` instead of refusing, which is this library's own
      # named defect: an empty answer standing in for a refusal.
      #
      # ★★ A GROUP DOES FORCE IT — every member's survival reads `rankOf` at every node of its
      # word, a singleton's included — so the reach this `seq` owns is the EMPTY case alone.
      # MEASURED by removing it: only the two empty-gather cells go radioactive. It stays, because
      # without it the order is forced at no reachable point of a query that gathers nothing.
      competed = builtins.seq effectiveOrder (
        map
          (
            grp:
            let
              branchesOf =
                c:
                let
                  s = map (step: step.label) c.path ++ [ "$" ];
                in
                builtins.genList (i: {
                  node = builtins.toJSON (builtins.genList (j: builtins.elemAt s j) i);
                  rank = effectiveOrder.rankOf (builtins.elemAt s i);
                }) (length s);
              minRank = builtins.mapAttrs (
                _: bs: foldl' (m: b: if b.rank < m then b.rank else m) (head bs).rank bs
              ) (builtins.groupBy (b: b.node) (concatMap branchesOf grp.members));
              survives = c: builtins.all (b: b.rank == minRank.${b.node}) (branchesOf c);
            in
            {
              inherit (grp) key;
              visible = filter survives grp.members;
              shadowed = filter (c: !(survives c)) grp.members;
            }
          )
          (
            groupsInWalkOrder (
              c:
              returned "viewRelation"
                "channel ${renderSubject def.name}'s competition key 'keyOf', for the contribution at scope ${renderSubject c.scope},"
                "a competition key is a string, because contributions sharing a key compete"
                builtins.isString
                (def.channel.keyOf c)
            ) contributions
          )
      );

      # 6a — the SPANNING REFUSAL, and 6b — the PER-GROUP ELEMENT COLLAPSE. AUTHORSHIP-VISIBILITY:
      # the element is the DECLARATION's, not the walk's, so it competes ONCE regardless of how
      # many paths reach it. This runs over `competed`'s `visible` ONLY — a contribution step 6
      # already shadowed never reaches an element check, or a declaration that competes cleanly
      # would be refused for a rival it already beat.
      #
      # 6a flattens every surviving contribution to a pair of ⟨its element key, its group's key⟩
      # and groups BY THE ELEMENT KEY. An element whose pairs carry more than one DISTINCT group
      # key spans groups: `k` split one authored declaration across two competitions, and nothing
      # downstream is handed a set `k` did not define (ADR-0024 ruling 5 — tie-set disposition is
      # within the group k defines, never across groups). Refused by name, not resolved by a
      # priority nobody declared.
      elementKeyOf =
        c:
        builtins.toJSON [
          c.element.producer
          c.element.ordinal
        ];

      spanningElements = filter (eg: length (groupsInWalkOrder (p: p.groupKeyStr) eg.members) > 1) (
        groupsInWalkOrder (p: p.elementKey) (
          concatMap (
            grp:
            map (c: {
              inherit c;
              groupKey = grp.key;
              groupKeyStr = builtins.toJSON grp.key;
              elementKey = elementKeyOf c;
            }) grp.visible
          ) competed
        )
      );

      # 6b runs only once 6a has passed, so every element left is visible under exactly one group:
      # the collapse is LOCAL to that group — `builtins.groupBy` its `visible` by the element key
      # and keep each sub-group's `head`, which `groupBy`'s own list-order-preservation makes the
      # WALK-FIRST arrival, matching a diamond minting exactly one element and a collision minting
      # two (distinct producers never share an element key).
      competedCollapsed =
        if spanningElements != [ ] then
          let
            eg = head spanningElements;
            groups = groupsInWalkOrder (p: p.groupKeyStr) eg.members;
            keys = map (g0: (head g0.members).groupKey) groups;
            c0 = (head eg.members).c;
          in
          refuse "viewRelation" "channel ${renderSubject def.name} declares a competition key that SPLITS one element: the datum authored at scope '${c0.element.producer}' (data entry ${toString c0.element.ordinal}) survives under ${toString (length keys)} competition keys (${quote (map builtins.toJSON keys)}), so one authored declaration would contribute once per key; a competition key must be constant over an element's arrivals, and the three contribution fields that can differ across them — admission, distance, path — are path-derived"
        else
          map (
            grp:
            grp
            // {
              visible = map (g0: head g0.members) (groupsInWalkOrder elementKeyOf grp.visible);
            }
          ) competed;

      tieRank =
        if def.tieSet.arm == "orderedFold" then
          builtins.listToAttrs (
            concatMap (
              i:
              let
                o = builtins.elemAt def.tieSet.order i;
              in
              if builtins.isString o then
                [
                  {
                    name = builtins.unsafeDiscardStringContext o;
                    value = i;
                  }
                ]
              else
                [ ]
            ) (builtins.genList (i: i) (length def.tieSet.order))
          )
        else
          { };
      rankOfScope =
        s:
        if builtins.isString s then
          tieRank.${builtins.unsafeDiscardStringContext s} or null
        else
          indexOf def.tieSet.order s;

      # 7 — the tie-set disposition.
      disposed = map (
        grp:
        if def.tieSet.arm == "union" then
          # The papers' own arm: the surviving-maximal set IS the answer, in walk order.
          grp
        else if def.tieSet.arm == "refuse" then
          (
            if length grp.visible > 1 then
              refuse "viewRelation" "channel ${renderSubject def.name} declares tieSet 'refuse' and the competition key ${builtins.toJSON grp.key} survives with ${toString (length grp.visible)} contributions, from scopes ${
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
            unranked = filter (c: rankOfScope c.scope == null) grp.visible;
          in
          if unranked != [ ] then
            refuse "viewRelation" "channel ${renderSubject def.name} declares tieSet 'orderedFold' whose declared order (${quote def.tieSet.order}) does not rank the contributing scope '${(head unranked).scope}'; the order is total over the surviving set"
          else
            grp
            // {
              visible = sort (x: y: rankOfScope x.scope < rankOfScope y.scope) grp.visible;
            }
      ) competedCollapsed;

      surviving = concatMap (grp: grp.visible) disposed;
      shadowed = concatMap (grp: grp.shadowed) disposed;

      # 8 — dedup, with EVERY DROP A RECORD. The surface this replaces declared a dedup and
      # enumerated no drops, so an answer that came back short could not be told from a
      # contribution that was never made.
      dedupKey =
        c:
        if def.dedup.arm == "byDatum" then
          bucketAddress c.datum
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
          # BY BUCKET, READ BACK IN WALK ORDER. Each survivor is tagged ONCE with its walk position,
          # its key and its bucket address; `builtins.groupBy` buckets them in one pass, keeping walk
          # order within a bucket. Per bucket, a fold keeps a candidate iff nothing KEPT BEFORE IT in
          # that bucket is `same`, and collapses it into the FIRST such kept element. `map` over the
          # tagged list then reads every decision back in walk order, so `kept` and `dropped` are
          # both in walk order. No accumulator is carried across the whole walk: a fold whose state
          # is `kept ++ [ c ]` or an attrset index `seen // { … }` copies that state on every step,
          # and both are quadratic in the group's size — on the one step whose whole purpose is to
          # make a large gather smaller.
          #
          # ★ THE ENCODING IS THE ADDRESS, NEVER THE DECISION. `idx` selects a BUCKET; what decides
          # survival is `same`, the relation the arm's own constructor declares — `byDatum` is
          # "structural equality on the datum itself" and `byKey` "a declared key", and in both SAME
          # means Nix `==`. Deciding on `builtins.toJSON` instead would record a drop asserting a
          # duplicate that does not exist: `toJSON` serialises an `outPath`/`__toString` attrset as
          # its string coercion, so `{ outPath = "X"; }` and `"X"` — Nix-distinct — encode alike.
          # The bucket scan is not the rescan rejected above for function-free data: bucket size is 1
          # for every such input that does not collide in the encoding, and those pay nothing extra.
          #
          # ★ FUNCTION-BEARING DATA COST Θ(b²), AND THAT IS A FLOOR. `bucketAddress` gives every
          # lambda one tag, so function-bearing survivors of one function-free skeleton share an
          # address and `same` is scanned pairwise within it: Θ(b²) comparisons for b such
          # survivors. No construction does better: the substrate has no function identity to
          # address by (`toJSON`, `toString` and `hashString` all reject a lambda), and deciding
          # duplicates with an equality test alone needs pairwise comparisons in the worst case
          # (element distinctness under an equality-only oracle). Measured step-8 increment over
          # `dedups.none` at 2000 / 4000 / 8000 such data: 0.61 s / 2.46 s / 11.1 s.
          #
          # ★ `==` OVER A LAMBDA IS CONSERVATIVE EQUALITY (Palmer 2024 §2.3): true only where the
          # lambdas are one binding (Nix compares by pointer first), false otherwise. A false only
          # keeps both, so every recorded drop stays licensed. A shared binding INSIDE a list or an
          # attrset collapses; a BARE lambda datum never does (`f == f` is false).
          #
          # ★ UNDER `byDatum`, `dropped.key` IS A BUCKET ADDRESS, NOT AN IDENTITY: two distinct
          # closures both read `[{"__lambda":null}]`. Do not key drops by it — ADR-0034 gives sealed
          # content no identity.
          #
          # ★ THE BOUND, stated where the construction is: `toJSON` is not a congruence for Nix
          # `==` (`1 == 1.0` is true while the encodings differ), so two data the declaration calls
          # the same can still land in different buckets and never meet. This decides SOUNDNESS —
          # every recorded drop is one the declaration licenses — and leaves COMPLETENESS exactly
          # as it was: a licensed collapse across encoding classes is still not made, and still not
          # recorded.
          let
            tagged = builtins.genList (
              i:
              let
                c = builtins.elemAt surviving i;
                k = dedupKey c;
              in
              {
                inherit i c k;
                idx = bucketAddress k;
              }
            ) (length surviving);
            same = t: s: if def.dedup.arm == "byDatum" then t.c.datum == s.c.datum else t.k == s.k;
            keptIn = builtins.mapAttrs (
              _: foldl' (acc: t: if builtins.any (same t) acc then acc else acc ++ [ t ]) [ ]
            ) (builtins.groupBy (t: t.idx) tagged);
            decided = map (t: t // { matches = filter (s: s.i < t.i && same t s) keptIn.${t.idx}; }) tagged;
          in
          {
            kept = map (t: t.c) (filter (t: t.matches == [ ]) decided);
            dropped = map (t: {
              contribution = t.c;
              collapsedInto = (head t.matches).c;
              policy = def.dedup.arm;
              key = t.k;
            }) (filter (t: t.matches != [ ]) decided);
          };

      # 9 — the fold, over the list AS IT STANDS: balanced bracketing under the declared
      # associativity, the list's order still the authority; no sort, no dedup by rank, no reorder.
      value = enums.foldCombine def.combine def.empty (map (c: c.datum) deduped.kept);

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
    if !(builtins.isFunction a.marks) then
      refuse "viewRelation" "field 'marks' is ${renderValue a.marks}; it must be a function from a scope id to the list of boundary marks at it"
    else if formalsOf a.marks != [ ] then
      refuse "viewRelation" "field 'marks' destructures an attrset (formals: ${quote (formalsOf a.marks)}); it is applied to a scope id, a string, so it can never be applied"
    else
      decided [ def g markOrder ] {
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
