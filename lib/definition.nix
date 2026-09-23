# THE VIEW DEFINITION — plain data, resolved in the structural stratum, EVERY FIELD REQUIRED AND
# TOTAL.
#
# ── THE TERM, AND EXACTLY WHAT IT IS LICENSED TO MEAN ────────────────────────────────────────
# Manchanda & Warren, "A Logic-based Language for Database Updates", chapter 10 of Minker (ed.)
# 1988, PRINTED 381, section *View Updates*:
#
#     "A database view is a rule-defined relation that is made to appear as a base relation
#      to the user."
#
# ★ CITE THE PRINTED-381 FORM WITH ITS PAGE. A near-duplicate at printed 365 reads "view relation
# is … appear LIKE a base relation"; without the page the citation is ambiguous.
#
# ★★ THE NARROWING IS PART OF THE CITATION AND IS NEVER DROPPED FROM IT. That chapter is
# view-UPDATE where what was wanted is view-MAINTENANCE, and no maintenance primary is held. It is
# cited as a DEFINITIONAL PRIMARY FROM ADJACENT LITERATURE AND NEVER AS MORE. This library
# derives; IT DOES NOT SOLVE THE UPDATE PROBLEM — there is no update translator here, no
# add/delete translator, and no update request is accepted against a derived result. The chapter's
# Definition 3 machinery is outside this library's subject.
#
# The two construct names below are that primary's own: `viewDefinition` names the DECLARATION
# ("view definition"), `viewRelation` names the RESULT ("view relation"). The ACT has no term at
# any held primary, so no identifier here names it.
#
# ── WHY EVERY FIELD IS REQUIRED ─────────────────────────────────────────────────────────────
# A DEFAULTED FIELD IS A DECISION NOBODY MADE AND NOBODY CAN SEE. Two of the fields below exist
# precisely because their absence used to be filled in silently: the competition key, whose
# shipped per-node default makes competition VACUOUS, and the distance rule, which a substrate
# that defaults it turns into a semantics nobody wrote down.
{ prelude, graph }:
let
  inherit (prelude) elem;
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  enums = import ./enumerations.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    decided
    quote
    renderValue
    ;
  inherit (carrierLib) elementOf;

  required = [
    # k AND the name of the result. One field at the composition surface — what competes is
    # exactly what is named — and a `dataOrder` element here, so the raw layer can say what the
    # composition cannot: that a registry competes per entity where a channel competes per channel.
    "channel"
    # r — the relation this view is ABOUT. The Q21 obligation: the relation sort is a first-class
    # carrier element, and a declaration that could not name a relation would have recorded that
    # ruling without building it. Checked against the graph's R at materialization, by name.
    "relation"
    # A scope of the one graph: where the walk starts.
    "root"
    "direction"
    # E — label well-formedness, as a constructed element carrying its own alphabet.
    "admission"
    # < — the label order, likewise.
    "order"
    # WFD — data term well-formedness. Fig. 1 names it a Visibility Parameter; gen's carrier does
    # not name it and ships it as the query's own predicate, so it rides on the DECLARATION rather
    # than in the carrier's five. It is required and not defaulted to the always-true predicate,
    # because "everything at the path's end is what I was looking for" is a decision and not an
    # absence.
    "wellFormed"
    # The distance rule: `{ distance; from; label; to; } → int`, handed the distance accumulated AT
    # the step's source together with the step. Plain hop count is `s: s.distance + 1`. Required
    # because the projection folds over it and a defaulted rule silently moves a distance.
    "distance"
    "tieSet"
    # The fold's unit, cross-checked against the combine arm's own. A declaration that states the
    # unit and a substrate that agrees or refuses is a checked declaration, which is the same shape
    # as the carrier's alphabet cross-check.
    "empty"
    "combine"
    "dedup"
  ];

  viewDefinition =
    args:
    let
      a = fields "viewDefinition" required args;
      admission = elementOf "viewDefinition" "admission" "labelWellFormedness" a.admission;
      order = elementOf "viewDefinition" "order" "labelOrder" a.order;
      channel = elementOf "viewDefinition" "channel" "dataOrder" a.channel;
      # ★ THE FIVE ARMS OF THE CONSTRUCTION-TIME DISCIPLINE ARE ALL ELEMENT-TAG CHECKS, and that is
      # the design rather than a coincidence. An unapplied `tieSets.orderedFold` is a FUNCTION, an
      # unapplied `combines.setUnion` is a FUNCTION, and a hand-written attrset carries no tag — so
      # "outside the three", "no declared order", "no declared ACC flag" and "outside the
      # whitelist" all reduce to one question the tag answers, asked at construction.
      tieSet = elementOf "viewDefinition" "tieSet" "tieSet" a.tieSet;
      combine = elementOf "viewDefinition" "combine" "combine" a.combine;
      dedup = elementOf "viewDefinition" "dedup" "dedup" a.dedup;
    in
    if !(builtins.isString a.relation) || a.relation == "" then
      refuse "viewDefinition" "field 'relation' must be a non-empty relation name; it is the r of (NR-Rel), reached once at the end of the path"
    else if !(builtins.isString a.root) || a.root == "" then
      refuse "viewDefinition" "field 'root' must be a non-empty scope id"
    else if !(elem a.direction enums.directions) then
      refuse "viewDefinition" "field 'direction' is ${renderValue a.direction}, which is not one of the declared arms (${quote enums.directions})"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "viewDefinition" "field 'wellFormed' must be a predicate on data terms; it is WFD, the parameter that decides whether the datum at the path's end is the one being looked for"
    else if !(builtins.isFunction a.distance) then
      refuse "viewDefinition" "field 'distance' must be a function `{ distance; from; label; to; } → int`; it is required because the projection folds over the distance it returns, and a defaulted rule is a semantics nobody wrote down"
    else if admission.alphabet.letters != order.alphabet.letters then
      refuse "viewDefinition" "'admission' and 'order' are built over different alphabets (${quote admission.alphabet.letters} vs ${quote order.alphabet.letters}); one definition has one L"
    # The three ARM checks are `elementOf`'s: its shape reads each arm through `choice` over the
    # declared arms, so a forged arm is refused at intake and never reaches a check here. The ACC
    # check below stays, because it is stricter than the shape (`acc` is a bool or null there).
    else if combine.setSemilattice && !(builtins.isBool combine.acc) then
      refuse "viewDefinition" "field 'combine' names the set-semilattice arm '${combine.arm}' with no declared ACC flag; write `combines.${combine.arm} { acc = <bool>; }`"
    else if a.empty != combine.unit then
      refuse "viewDefinition" "field 'empty' is ${renderValue a.empty}, which is not the unit of the declared combine arm '${combine.arm}' (${renderValue combine.unit}); a fold whose seed is not its operation's unit is not the fold it declares"
    else
      decided
        [
          channel
          tieSet
          combine
          dedup
        ]
        {
          __element = "viewDefinition";
          inherit
            admission
            order
            channel
            tieSet
            combine
            dedup
            ;
          inherit (a)
            relation
            root
            direction
            wellFormed
            distance
            empty
            ;
          # The name of the result, lifted out of the key element so a reader of the definition does
          # not have to know that the two are one field.
          name = channel.channel;
        };
in
{
  inherit viewDefinition required;
}
