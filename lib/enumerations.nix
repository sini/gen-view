# THE CLOSED ENUMERATIONS A VIEW DEFINITION DRAWS FROM — combines, tie-set dispositions, dedup
# policies and walk directions. Each arm is a CONSTRUCTED value, so a declaration naming one has
# already passed that arm's own checks before the definition sees it.
#
# ★★ WHY `combine` IS A WHITELIST AND NOT A CALLER-SUPPLIED FUNCTION. The ground is the cascade's
# own: ACC IS UNDECIDABLE FROM AN ARBITRARY COMBINE, SO IT IS A DECLARED CARRIER PROPERTY AND NOT
# AN INFERRED ONE. A library that accepted any binary function would be accepting a carrier
# property it cannot check and cannot ask about, and would then have to either assume the property
# (unsound) or refuse every fold (useless). A closed set of arms, each carrying its associativity
# and its unit as declarations, is what makes the property answerable at all.
#
# ★ THE SHAPE IS RE-DERIVED, NOT THE IMPLEMENTATION. The reference/cascade grammar is ruled out
# for this surface, so what is inherited here is the LAW — a declared associativity property and a
# declared ACC flag on the semilattice arm — and not that grammar's enforcement machinery.
{ prelude }:
let
  inherit (prelude) unique;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    decided
    strings
    renderSubject
    quote
    ;

  # ── COMBINES ────────────────────────────────────────────────────────────────────────────────
  # Each arm declares: its binary operation, its UNIT, whether it is ASSOCIATIVE, and whether it
  # is a SET SEMILATTICE. The semilattice arm additionally requires the caller to declare the ACC
  # flag, which is why it is a FUNCTION where the others are values: an unapplied arm is not a
  # combine record, so "a set-semilattice combine with no declared ACC flag" is refused by the
  # same check that refuses a combine from outside the whitelist, and no separate flag hunt is
  # needed.
  mkCombine =
    {
      arm,
      op,
      unit,
      associative,
      setSemilattice,
      acc,
    }:
    {
      __element = "combine";
      inherit
        arm
        op
        unit
        associative
        setSemilattice
        acc
        ;
    };

  combines = {
    # THE LINEAR CARRIER. Concatenation: associative, NOT commutative, NOT idempotent — which is
    # exactly why the fold over it may not reorder and may not dedup by rank. The list's order is
    # the authority.
    listAppend = mkCombine {
      arm = "listAppend";
      op = a: b: a ++ b;
      unit = [ ];
      associative = true;
      setSemilattice = false;
      acc = null;
    };

    # THE SHALLOW RECORD MERGE. Associative, right-biased, not commutative. Its unit is the empty
    # attrset.
    attrsShallow = mkCombine {
      arm = "attrsShallow";
      op = a: b: a // b;
      unit = { };
      associative = true;
      setSemilattice = false;
      acc = null;
    };

    # THE SET SEMILATTICE — order-preserving union under structural equality: associative,
    # commutative up to the order it preserves, and IDEMPOTENT. Idempotence is what makes it a
    # semilattice and what makes the ACC question meaningful, so this arm and only this arm takes
    # the flag.
    #
    # ★ THE FLAG IS THE CALLER'S CLAIM ABOUT THE VALUE DOMAIN, NOT ABOUT THE OPERATION. Union over
    # a finite domain satisfies the ascending chain condition; union over an unbounded one need
    # not, and no inspection of the operation can tell which domain a caller is folding. That is
    # the undecidability the whitelist exists to convert into a declaration.
    #
    # The retiring `gen-resolve.cascade` admitted `combine = "semilattice-set"` only on a
    # declared `acc = true`, and its assert checked that the caller had SET the boolean — no
    # associativity, no idempotence, no finite height. That construct's ACC flag survives here
    # and nowhere else.
    #
    # **What this surface DECIDES, and it is Datafun §9's own answer.** The `combineArms`
    # whitelist closes the set of admissible operations; an arbitrary caller-supplied combine
    # is refused because the ascending chain condition is undecidable from one. That half is
    # enforced, not declared.
    #
    # **What this surface still only DECLARES.** `acc` is a claim about the fold's VALUE
    # DOMAIN, and no inspection of the operation reaches it. Union over a finite domain
    # satisfies ACC; union over an unbounded one need not. A false `acc = true` is not caught
    # here and diverges at the fold.
    #
    # **The ecosystem's answer to the same question, where it HAS one, and it is not this
    # shape.** gen-scope's `circular` attribute takes a carrier declaring `{ bottom, leq,
    # height, quotient }`, derives the iteration bound `Σ hᵢ + 1` from it, and refuses BY NAME
    # both when the step does not ascend the declared order and when the declared height is
    # exceeded — refuting the DECLARATION, never clamping to a budget. That is Datafun's
    # `FIX≤` without `FIX≤`'s silent truncation. Nothing of that shape exists for a fold's
    # value domain, and constructing one is open work, not a residue this comment discharges.
    #
    # **Why a declaration and not a bound was the original choice, recorded because the reason
    # is not the one a reader reconstructs.** Undecidability alone equally licenses a bound,
    # and a bound that CLAMPS fails silently (`den-hoag-dtfn`). Declaration was chosen because
    # the failure it produces — divergence — cannot hide. gen-scope's construction shows the
    # third option: a declared bound that is CHECKED and REFUTED loudly. Whether this surface
    # should take it is `den-hoag-uxnf`'s question, and it is open.
    #
    # ANCHOR: R10.1-RIDER-ACC-VALUE-DOMAIN
    setUnion =
      args:
      let
        a = fields "combines.setUnion" [ "acc" ] args;
      in
      if !(builtins.isBool a.acc) then
        refuse "combines.setUnion" "acc must be a bool; it is the ascending-chain-condition flag for this fold's value domain, and it is declared because it cannot be inferred from the operation"
      else
        setUnionOf a.acc;
  };

  # ★ THE UNION CARRIES A STRING'S TWINS' CONTEXTS (den-hoag-kunjm F2, the quotient rule's string
  # half): `==` is blind to string context, so a string element collapsed with `==`-equal twins
  # carries the union of their contexts, which is Nix's own concatenation. Context union is
  # associative and commutative and `unique` keeps first-occurrence order, so every bracketing the
  # fold chooses gives one result wherever `==` is an equivalence on the elements (for strings it
  # is text equality). Strings go by a text-keyed table, linear as `unique`'s own string path.
  #
  # ★ A NON-STRING UNION COLLAPSE IS A STATED BOUNDARY, NOT A CHECK: it keeps the walk-first
  # element as it stood and drops a twin's context silently, as before the rule. Reading a
  # non-string element's edges is a walk of datum content, which is not total here (a pointer-shared
  # cyclic element overflows the stack uncatchably, a lazily-throwing attribute is forced, where
  # `unique`'s `==` shortcuts on pointer identity and forces neither), and a bound on that walk would
  # refuse deep valid input (ADR-0032). Pending an owner reading; den-hoag-gkrtw retires it.
  setUnionOf =
    acc:
    mkCombine {
      arm = "setUnion";
      op =
        a': b':
        let
          xs = a' ++ b';
          byText = builtins.groupBy builtins.unsafeDiscardStringContext (
            builtins.filter builtins.isString xs
          );
          twinsOf =
            r:
            if builtins.isString r then builtins.tail byText.${builtins.unsafeDiscardStringContext r} else [ ];
        in
        if builtins.length xs < 2 then xs else map (r: absorb unionSite r (twinsOf r)) (unique xs);
      unit = [ ];
      associative = true;
      setSemilattice = true;
      inherit acc;
    };

  unionSite = {
    fn = "combines.setUnion";
    subject = "the set union";
    at = "";
  };

  # ── THE QUOTIENT RULE (den-hoag-kunjm) ──────────────────────────────────────────────────────
  # A collapse of data equal under `==` but differing in string context identifies nodes, and a
  # quotient keeps the incident edges it can read: the kept datum carries the UNION of its twins'
  # dependency edges where it can carry them, and a collapse that would visibly lose one is refused.
  # Both `==`-collapsing sites, step 8's dedup and the set union above, route through `absorb`; the
  # union reaches it with string twins only. The stated boundaries (README, "Dedup and string
  # context") are where an edge is dropped silently. den-hoag-gkrtw replaces this with the general
  # quotient, and its refusals and boundaries retire.

  # `edgesOf v` — the dependency edges of `v`, as one empty string carrying their union. It stops
  # at a coercion, where step 8's bucket address (`toJSON`) stops, and in `toJSON`'s priority: a
  # `__toString` set is read through its string, else a set with `outPath` through it (so a
  # derivation, which refers to itself, is never walked). Functions, paths, numbers, bools and null
  # carry no context.
  edgesOf =
    v:
    if builtins.isString v then
      builtins.substring 0 0 v
    else if builtins.isList v then
      builtins.concatStringsSep "" (map edgesOf v)
    else if builtins.isAttrs v then
      if v ? __toString then
        builtins.substring 0 0 (toString v)
      else if v ? outPath then
        edgesOf v.outPath
      else
        builtins.concatStringsSep "" (map (n: edgesOf v.${n}) (builtins.attrNames v))
    else
      "";

  # `uncertified v` — whether `v` holds a coercible set that is not a derivation and has attributes
  # besides its coercion. `edgesOf` stops at the coercion, so a context in such a sibling is an edge
  # it cannot read, and no collapse of `v` can certify that it carries it. The coercion is the one
  # `edgesOf` reads, in `toJSON`'s priority, so the `outPath` of a set that also has `__toString` is
  # a sibling like any other, and an `outPath` that is itself a set is followed, as `edgesOf`
  # follows it. A derivation is a set typed `"derivation"` WITH an `outPath` (Nix `==` compares one
  # by its `outPath`); its other attributes are not read, so a context held beside a derivation's
  # `outPath` is dropped silently, a stated boundary. Reading a sibling instead is not total (a
  # flake input recurses, a pointer-shared cyclic set overflows, both uncatchably). ★ A SHAPE
  # CHECK, run only at step 8 `byDatum`, whose bucket address has already walked the datum: it
  # reads attribute NAMES and a set's `type` and forces no sibling's value.
  uncertified =
    v:
    if builtins.isList v then
      builtins.any uncertified v
    else if builtins.isAttrs v then
      if (v.type or null) == "derivation" && v ? outPath then
        false
      else if v ? __toString then
        builtins.attrNames (removeAttrs v [ "__toString" ]) != [ ]
      else if v ? outPath then
        builtins.attrNames (removeAttrs v [ "outPath" ]) != [ ] || uncertified v.outPath
      else
        builtins.any (n: uncertified v.${n}) (builtins.attrNames v)
    else
      false;

  # `absorb site kept twins` — `kept` carrying its `==`-equal `twins`' edges, or a named refusal.
  # A string carries the union by its context, which is Nix's own concatenation. A non-string
  # cannot, so a collapse that would lose an edge is refused; so is any collapse holding a shape
  # whose edges cannot be read (`uncertified`), whatever it carries.
  absorb =
    {
      fn,
      subject,
      at,
    }:
    kept: twins:
    let
      lost = builtins.concatStringsSep "" (map edgesOf twins);
    in
    if twins == [ ] then
      kept
    else if uncertified kept then
      refuse fn "${subject} collapses a datum${at} holding a coercible set that is not a derivation and has attributes besides its coercion; a store dependency there is an edge the collapse cannot read, so it cannot carry it (den-hoag-gkrtw retires this refusal)"
    else if !(builtins.hasContext lost) then
      kept
    else if builtins.isString kept then
      builtins.appendContext kept (builtins.getContext lost)
    else if builtins.getContext (edgesOf kept + lost) == builtins.getContext (edgesOf kept) then
      kept
    else
      refuse fn "${subject} collapses a non-string datum${at} with ${toString (builtins.length twins)} `==`-equal twin(s) whose store dependencies it does not carry (${quote (builtins.attrNames (removeAttrs (builtins.getContext lost) (builtins.attrNames (builtins.getContext (edgesOf kept)))))}); a collapse keeps its twins' dependency edges, and only a string can carry the union (den-hoag-gkrtw retires this refusal)";

  # `combineOf combine` — the combine record its checked `arm` decides, read from the whitelist
  # table. `op`, `unit`, `associative` and `setSemilattice` are the ARM's, so every reader runs
  # THIS and never reads them off the element (den-hoag-6vsvx): a forged one is inert and the
  # enforced whitelist cannot be bypassed by an `op` riding a whitelisted tag. `acc` is the
  # caller's declaration about the value domain, which no arm decides, so it is carried as given.
  # The arm is intake's to check (`elements.nix` shape `combine`). O(1).
  combineOf =
    combine: if combine.arm == "setUnion" then setUnionOf combine.acc else combines.${combine.arm};

  combineArms = [
    "listAppend"
    "attrsShallow"
    "setUnion"
  ];

  # `foldCombine combine empty xs` — step 9's fold, the ONE declaration both step-9 sites use
  # (`viewRelation`'s `value` and `transform`'s `refold`), so they cannot drift apart.
  #
  # ★★ A BALANCED BRACKETING, LICENSED BY THE ARM'S DECLARED ASSOCIATIVITY AND NOTHING ELSE. B5's
  # own statement is gen-pipe REFERENCE.md L1: "Left fold in the pinned canonical traversal under
  # the associative-only combine. No silent reorder, no silent dedup." Under an associative `op`
  # every bracketing of one sequence has one value, so "left fold" fixes the VALUE and not an
  # evaluation order: pairing adjacent elements level by level keeps every left operand earlier in
  # the list than its right one, and keeping `empty` leftmost makes the result equal
  # `foldl' op empty xs` without leaning on the unit law. Nothing is sorted, deduped or reordered.
  #
  # ★ WHY NOT `foldl'`. Under `listAppend` (and `//` under `attrsShallow`) a left fold copies the
  # accumulator on every step, Θ(N²) in the list's length. This is Θ(N log N), and its recursion
  # depth is ⌈log₂ N⌉ levels rather than a WHNF chain N deep.
  #
  # ★ THE ARM'S DECLARATION IS READ, NOT ASSUMED. `op` and `associative` come from the arm's own
  # entry in the whitelist table (`combineOf`), never from the element. A table arm that does not
  # declare `associative = true` is refused by name, because re-bracketing it would change its
  # answer silently.
  foldCombine =
    combine: empty: xs:
    let
      c = combineOf combine;
      op = c.op;
      pairUp =
        ys:
        let
          m = builtins.length ys;
        in
        builtins.genList (
          i:
          if 2 * i + 1 < m then
            op (builtins.elemAt ys (2 * i)) (builtins.elemAt ys (2 * i + 1))
          else
            builtins.elemAt ys (2 * i)
        ) ((m + 1) / 2);
      go = ys: if builtins.length ys == 1 then builtins.head ys else go (pairUp ys);
    in
    if c.associative != true then
      refuse "foldCombine" "the combine arm ${renderSubject c.arm} does not declare associative = true; step 9 re-brackets its fold, which B5 (gen-pipe L1) licenses under an associative-only combine and no other"
    else
      go ([ empty ] ++ xs);

  # ── TIE-SET DISPOSITIONS ────────────────────────────────────────────────────────────────────
  # Every declaration names its per-channel tie-set disposition, because the SURVIVING-MAXIMAL SET
  # is where specificity hands off to the merge that follows it, and a coarser order grows that
  # merge's domain. The boundary holds only when the disposition is named.
  #
  # ★ EXACTLY THREE ARMS, EACH WITH ITS ARGUMENT. The scope-graph papers make visibility a
  # PREDICATE YIELDING A SET (Néron, Tolmach, Visser & Wachsmuth 2015 §2.2: the calculus
  # identifies ALL the resolutions), so `union` is theirs directly: the surviving set IS the answer.
  #
  # `refuse` is not a per-contribution outcome, which no primary has; it is a VERDICT ON THE SIZE
  # of the calculus's answer set, and the primaries state that verdict, outside the calculus:
  # van Antwerpen et al. 2018, printed 114:9 (a field reference "resolves to a single
  # declaration") and 114:20 ("the result of resolution must be a single declaration-type pair");
  # van Antwerpen et al. 2016 §3.4 (a reference resolvable two ways "is ambiguous and can be
  # flagged as an error"). So `refuse` is `union` plus that singleton verdict: equal to it on a
  # one-survivor group, a refusal on a tie.
  #
  # `orderedFold` is a fold of the survivors in the FORM of Van Wyk et al. 2010 §2.2, printed 12,
  # `vᵢ ⊕ v₁ ⊕ … ⊕ vₙ` with ⊕ associative and not required to be commutative. Its ORDER is not
  # Silver's: Silver declined to make it specifiable ("the order … is not specifiable in Silver
  # and thus this order must not matter"). The authority for a DECLARED order is ADR-0029's
  # positional-authority ruling, as amended by ADR-0024 ruling 5, and stated as that ruling, not
  # as a primary: it stands while ADR-0029 does, and ADR-0029 is open to reconsideration. Its
  # precondition — an order invariant under presentation order — is met by construction below.
  tieSets = {
    # The papers' own: the surviving-maximal set IS the answer.
    union = {
      __element = "tieSet";
      arm = "union";
      order = null;
    };

    # More than one survivor is a refusal naming the channel and the tied contributions.
    refuse = {
      __element = "tieSet";
      arm = "refuse";
      order = null;
    };

    # ★ THE ORDER MUST BE A DECLARED TOTAL ORDER, INVARIANT UNDER PRESENTATION ORDER, AND NEVER
    # DERIVED FROM A KIND HIERARCHY. It is a list of contribution keys, written down: a list is
    # invariant under presentation order by construction, where a comparator over arrival position
    # is not.
    #
    # ★★ ARRIVAL ORDER IS REFUSED AT CONSTRUCTION, AND `order = null` IS ITS SPELLING. A
    # declaration migrating from a grammar that had no declared order arrives with nothing to say
    # here, and the tempting reading of "nothing" is "the order they arrived in" — under which the
    # ordered-fold ruling and the presentation-invariance ruling collide head-on. So the absence is
    # refused by name rather than interpreted: absence is a decision, and this is the decision it
    # is not allowed to be.
    orderedFold =
      args:
      let
        a = fields "tieSets.orderedFold" [ "order" ] args;
      in
      if a.order == null then
        refuse "tieSets.orderedFold" "order is null, which spells ARRIVAL ORDER; an ordered fold's order must be a declared total order, invariant under presentation order — under arrival order the ordered-fold ruling and the presentation-invariance ruling collide head-on"
      else if !(builtins.isList a.order) then
        refuse "tieSets.orderedFold" "order must be a list of declared contribution keys, most-significant first; a comparator over arrival position is not invariant under presentation order, and a kind hierarchy is not a declaration"
      else if a.order == [ ] then
        refuse "tieSets.orderedFold" "order is empty; an ordered fold with no declared order disposes its surviving set by nothing"
      else
        let
          order = strings "tieSets.orderedFold" "order" a.order;
        in
        decided [ order ] {
          __element = "tieSet";
          arm = "orderedFold";
          inherit order;
        };
  };

  tieSetArms = [
    "union"
    "refuse"
    "orderedFold"
  ];

  # ── DEDUP POLICIES ──────────────────────────────────────────────────────────────────────────
  # Required for every declaration that uses the linear carrier — that is, all of them.
  #
  # ★ EVERY DROP IS A RECORD. The surface this replaces DECLARED a dedup and did not enumerate its
  # drops, so a caller whose answer came back short had no way to tell a dedup collapse from a
  # contribution that was never made. The materialized result carries `dropped`, and the policy is
  # what decides which entries land there.
  dedups = {
    none = {
      __element = "dedup";
      arm = "none";
      keyOf = null;
    };
    # Structural equality on the datum itself.
    byDatum = {
      __element = "dedup";
      arm = "byDatum";
      keyOf = null;
    };
    # A declared key, for a domain where two structurally distinct datums are the same thing.
    byKey =
      args:
      let
        a = fields "dedups.byKey" [ "keyOf" ] args;
      in
      if !(builtins.isFunction a.keyOf) then
        refuse "dedups.byKey" "keyOf must be a function from a contribution to its dedup key"
      else
        {
          __element = "dedup";
          arm = "byKey";
          inherit (a) keyOf;
        };
  };

  dedupArms = [
    "none"
    "byDatum"
    "byKey"
  ];

  # ── DIRECTIONS ──────────────────────────────────────────────────────────────────────────────
  # ★ `direction` IS DERIVED, NOT ADDED. The inbound arm is the calculus's own query over the
  # LABELLED CONVERSE of `edges(G|M)` — the graph after its boundary marks — and `data(G)` does not
  # transpose. van Antwerpen et al. 2018 Fig. 1's `Edges ::= s l s` is closed under the converse,
  # so the converse is a scope graph and the query over it is the calculus's query; Mokhov 2017
  # §5.2 (Graph Transpose) is the graph operation, lifted pointwise per label. ADR-0010 §1 names
  # the same dual: "the inverse read is the same edge set queried from the other end". So the field
  # is kept and defined AS that derivation, and the marks bound G before the converse is taken
  # (`relation.nix`, steps 1 and 2).
  #
  # The mechanism is a labelled transpose, which reverses direction rather than erasing it: a
  # label is carried BY an edge, so flipping the edge relation moves the label with it. Reaching
  # the plain transpose through a label-forgetting projection erases precisely the component the
  # walk reads, which is why that composition is not a labelled transpose.
  directions = [
    "outbound"
    "inbound"
  ];
in
{
  inherit
    combines
    combineOf
    combineArms
    foldCombine
    absorb
    tieSets
    tieSetArms
    dedups
    dedupArms
    directions
    ;
}
