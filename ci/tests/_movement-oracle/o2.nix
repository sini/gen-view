# AC-7 / O2 — SENSITIVITY, arm by arm, with the permutation CONTROL.
#
# One acceptance topology (AC-9(iv)'s — the shared fixture, `L = { parent, include }`,
# `admission = (parent|include)*`, reaching a datum across an `include` edge) perturbed in EACH way
# the carrier can differ, per R§9.2 revision 2:
#
#   a  a changed WFL for one relation          `(parent|include)*` → `parent*`
#   b  a changed admission DOMAIN              the relation the admission is FOR: `import` → `policy`
#   c  a different competition key k            per-channel → per-scope
#   d  a different tieSet                      `union` → `orderedFold`
#   e  a boundary mark added                   the `no-containment` mark on `leaf`
#
# ★ (a) AND (b) ARE SEPARATE ARMS BECAUSE THEY MOVE THE REACHED SET INDEPENDENTLY, which is exactly
# what revision 2 added them for: (a) changes WHICH SCOPES the walk reaches, (b) changes WHICH
# DATUMS are read at the scopes it reached. An arm varying only one leaves the other unmeasured.
#
# ★ HOW (b) IS EXPRESSED AT THIS DESTINATION, STATED RATHER THAN ASSUMED. The spec's `admission` is
# a MAP from relation to WFL, so its DOMAIN is a set of relation names. gen-view's `viewDefinition`
# carries ONE `admission` element and ONE `relation`, so the declaration's admission domain is the
# singleton `{ relation }` and changing the domain is changing `relation`. The mapping is recorded
# here because it is a re-expression and not an identity.
#
# ★ THE HASH HALF IS gen-view's OWN `hashTrace`. AC-7 ran this arm through a map into the frozen edge
# record; spec §9.5 re-scoped that instrument to topology evidence and ADR-0010 §3 retired its
# library, so the fingerprint read here is the destination's — the one the oracle cluster moved to.
{ genView, fixture }:
let
  v = genView;
  f = fixture;

  placement = v.placement.place {
    mode = "nest";
    path = [ "settings" ];
    name = "settings";
    value = null;
  };

  hashOf = relation: v.hashTrace { inherit relation placement; };
  answerOf = relation: relation.value;
  shapeOf = relation: {
    hash = hashOf relation;
    answer = answerOf relation;
    contributions = builtins.map (c: {
      inherit (c)
        scope
        distance
        relation
        admission
        ;
      word = builtins.map (s: s.label) c.path;
    }) relation.contributions;
  };

  # ── THE BASE ────────────────────────────────────────────────────────────────────────────────
  base = f.relation;

  # ── THE FIVE ARMS ───────────────────────────────────────────────────────────────────────────
  armA_wfl = f.mkRelation {
    definition = f.mkDefinition {
      admission = v.labelWellFormedness {
        alphabet = f.labels;
        expression = "parent*";
      };
      order = f.order;
    };
  };

  armB_domain = f.mkRelation { definition = f.mkDefinition { relation = "policy"; }; };

  armC_key = f.mkRelation {
    definition = v.viewDefinition (f.definitionArgs // { channel = f.perScopeKey; });
  };

  armD_tieSet = f.mkRelation {
    definition = f.mkDefinition {
      tieSet = v.tieSets.orderedFold {
        order = [
          "inc"
          "leaf"
          "mid"
          "root"
        ];
      };
    };
  };

  armE_mark = f.mkRelation { marks = f.includeMark; };

  # ── THE PERMUTATION CONTROL ─────────────────────────────────────────────────────────────────
  # A PURE PERMUTATION OF DECLARATION ORDER must leave `hashTrace` BYTE-EQUAL. Three presentation
  # axes are permuted at once, none of them semantic:
  #   · the `data` component's list order (the same triples, written in reverse)
  #   · the `scopes` list order
  #   · the `relations` name-set order
  # ★ WHAT IS NOT PERMUTED, AND WHY: the label ORDER's layers and the tieSet's declared order are
  # SEMANTIC lists — permuting one is arm (d) or a different order, not a presentation change.
  permutedRelations = v.relations {
    names = [
      "policy"
      "broadcast-in"
      "expose-in"
      "import"
    ];
  };
  permutedCarrier = v.carrier {
    labels = f.labels;
    relations = permutedRelations;
    relatumLabels = f.roles;
    labelWellFormedness = f.admission;
    labelOrder = f.order;
    dataOrder = f.key;
  };
  reverse =
    xs: builtins.genList (i: builtins.elemAt xs (builtins.length xs - 1 - i)) (builtins.length xs);
  permutedGraph = v.scopeGraph {
    carrier = permutedCarrier;
    scopes = reverse f.scopes;
    edges = f.edges;
    data = reverse (f.authored f.datums);
  };
  permuted = f.mkRelation { graph = permutedGraph; };

  # ★ THE CONTROL'S OWN CONTROL: the permutation must be a REAL permutation. If the two data lists
  # were already equal, byte-equality would prove nothing.
  permutationIsReal = (f.authored f.datums) != (reverse (f.authored f.datums));
  scopePermutationIsReal = f.scopes != reverse f.scopes;

  # ── THE SECOND HALF OF THE PAIR ─────────────────────────────────────────────────────────────
  # R§9.2 defines the acceptance oracle as the PAIR ⟨`hashTrace` over the mapped topology, the
  # MATERIALIZED CHANNEL VALUE⟩. The arms above measure sensitivity of the FIRST half only; this
  # measures the second on the SAME topology pairs, so each arm reports both.
  #
  # ★ THE COMPARISON IS THREE-VALUED AND `not-evaluable` IS A REAL OUTCOME, NOT A FORMALITY. A
  # movement declaration may REFUSE at materialization — `tieSet = refuse` throws when more than one
  # contribution survives — and a refused run has no channel value to compare. Collapsing that into
  # "byte-equal" would report a refusal as agreement, which is the silent-vanish shape one level up.
  # It is measured through `tryEval` over a `deepSeq` of BOTH values, and `valueControls` below
  # carries a case that genuinely lands there, so the third arm is not a dead category.
  #
  # ★ AND "BYTE-EQUAL" IS MEANT LITERALLY: the comparison is over `builtins.toJSON` of each value,
  # not over Nix structural equality, so the word in the report is the measurement that was taken.
  valueCompare =
    x: y:
    let
      probe = builtins.tryEval (builtins.deepSeq [ x y ] (builtins.toJSON x == builtins.toJSON y));
    in
    if !probe.success then
      "not-evaluable"
    else if probe.value then
      "byte-equal"
    else
      "differs";

  valuePairs = {
    a_changed_WFL = armA_wfl;
    b_changed_admission_domain = armB_domain;
    c_different_competition_key = armC_key;
    d_different_tieSet = armD_tieSet;
    e_boundary_mark_added = armE_mark;
  };

  # THE CONTROL FOR THE `not-evaluable` ARM. `tieSet = refuse` on the FLAT-ORDER base, whose
  # surviving set has TWO members: the declaration asked for exactly one, so materialization refuses
  # by name and there is no channel value. If this row read anything but `not-evaluable`, the
  # three-valued comparison would be two-valued in disguise.
  flatRefuse = f.mkRelation {
    definition = f.mkDefinition {
      order = f.flatOrder;
      tieSet = v.tieSets.refuse;
    };
  };

  arms = {
    base = shapeOf base;
    a_changed_WFL = shapeOf armA_wfl;
    b_changed_admission_domain = shapeOf armB_domain;
    c_different_competition_key = shapeOf armC_key;
    d_different_tieSet = shapeOf armD_tieSet;
    e_boundary_mark_added = shapeOf armE_mark;
  };

  control = {
    baseHash = hashOf base;
    permutedHash = hashOf permuted;
    byteEqual = hashOf base == hashOf permuted;
    inherit permutationIsReal scopePermutationIsReal;
    baseAnswer = base.value;
    permutedAnswer = permuted.value;
    # THE SECOND HALF's CONTROL, measured in the SAME run: a pure permutation must leave the
    # MATERIALIZED VALUE byte-equal too. A permutation that moved the value would mean the
    # "presentation only" claim was false and every arm's value column would be reading noise.
    valueComparison = valueCompare base.value permuted.value;
  };

  # The value half, arm by arm, against the same base the hash column uses.
  valueVerdict = builtins.mapAttrs (_: r: valueCompare base.value r.value) valuePairs;

  valueControls = {
    # ★ THE POSITIVE CONTROL ON `differs`: two runs known to answer differently must read `differs`.
    knownDifferent = valueCompare base.value armA_wfl.value;
    # ★ THE POSITIVE CONTROL ON `byte-equal`: a value compared against itself must read `byte-equal`.
    knownEqual = valueCompare base.value base.value;
    # ★ THE POSITIVE CONTROL ON `not-evaluable`: a declaration that REFUSES at materialization has
    # no channel value, and the comparison must say so rather than collapse to agreement.
    knownRefusing = valueCompare base.value flatRefuse.value;
  };

in
{
  inherit
    arms
    control
    valueVerdict
    valueControls
    ;
  verdict = builtins.mapAttrs (_: a: {
    inherit (a) hash answer;
    differsFromBase = a.hash != arms.base.hash;
  }) arms;
}
