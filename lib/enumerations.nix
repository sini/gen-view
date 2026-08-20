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
  inherit (refusal) refuse fields strings;

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
    setUnion =
      args:
      let
        a = fields "combines.setUnion" [ "acc" ] args;
      in
      if !(builtins.isBool a.acc) then
        refuse "combines.setUnion" "acc must be a bool; it is the ascending-chain-condition flag for this fold's value domain, and it is declared because it cannot be inferred from the operation"
      else
        mkCombine {
          arm = "setUnion";
          op = a': b': unique (a' ++ b');
          unit = [ ];
          associative = true;
          setSemilattice = true;
          inherit (a) acc;
        };
  };

  combineArms = [
    "listAppend"
    "attrsShallow"
    "setUnion"
  ];

  # ── TIE-SET DISPOSITIONS ────────────────────────────────────────────────────────────────────
  # Every declaration names its per-channel tie-set disposition, because the SURVIVING-MAXIMAL SET
  # is where specificity hands off to the merge that follows it, and a coarser order grows that
  # merge's domain. The boundary holds only when the disposition is named.
  #
  # ★ EXACTLY THREE ARMS, AND TWO OF THEM STILL OWE THEIR ARGUMENTS. The scope-graph papers make
  # visibility a PREDICATE YIELDING A SET, so only `union` is theirs: no primary has a
  # per-contribution outcome beyond set membership. `refuse` and `orderedFold` are this
  # ecosystem's own, carried unchanged because they are ruled into the declaration — and
  # `orderedFold`'s debt is the larger one, because it asserts a DECLARATION-ORDER AUTHORITY
  # STRONGER THAN a primary that CONSIDERED the question and declined it: "the operator does not
  # have to be commutative, [but] the order … is not specifiable in Silver and thus this order
  # must not matter." An argument for `orderedFold` has to beat a refusal, which is a higher bar
  # than filling a gap. The debt is recorded here so a later retirement has something to land
  # against; it is not discharged here and nothing in this file may be read as discharging it.
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
        {
          __element = "tieSet";
          arm = "orderedFold";
          order = strings "tieSets.orderedFold" "order" a.order;
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
  # ★ `direction` HAS NO COUNTERPART IN THE CALCULUS AND STILL OWES ITS ARGUMENT. It is carried
  # unchanged because it is ruled into the declaration, and a spec that quietly dropped a ruled
  # field would be the silent-drop class. Recorded here, not discharged here.
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
    combineArms
    tieSets
    tieSetArms
    dedups
    dedupArms
    directions
    ;
}
