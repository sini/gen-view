# THE EXPORT SURFACE, PINNED BY CONTENTS — and pinned in TWO LAYERS, because the two-layer
# publication is the design and not a presentation choice.
#
# ★★ THE RAW LAYER IS THE ONE THAT MATTERS HERE. The constructs of this library migrate into a
# consolidated library later and the container does not, so a construct that is only reachable
# THROUGH a composition would have to be rebuilt at the fold, while a published one moves intact.
# This suite is what makes "published" a checked fact: an element quietly demoted to an internal
# binding, reachable only as a side effect of calling a composition, takes a cell red here rather
# than being noticed at the fold.
{ genView, ... }:
let
  v = genView;
in
{
  flake.tests.surface = {
    # The whole surface, sorted. A rename or a drop is intentional and moves this list in the same
    # commit; anything else is drift.
    test-the-published-surface = {
      expr = builtins.attrNames v;
      expected = [
        "accumulatorOrder"
        "accumulatorRelation"
        "arrivalMode"
        "arrivalModes"
        "authoredAt"
        "carrier"
        "carrierElements"
        "cell"
        "combineArms"
        "combines"
        "compositionFields"
        "compositions"
        "dataOrder"
        "dedupArms"
        "dedups"
        "definitionFields"
        "directions"
        "edgeLabels"
        "edgeSortKey"
        "emittedAt"
        "labelOrder"
        "labelWellFormedness"
        "orderedFoldOf"
        "placement"
        "readsOf"
        "relationLookup"
        "relations"
        "renderEntry"
        "renderTrace"
        "scopeGraph"
        "severedAt"
        "tieSetArms"
        "tieSets"
        "trace"
        "traceEntryOf"
        "transform"
        "unit"
        "viewDefinition"
        "viewRelation"
        "writesOf"
      ];
    };

    # ── THE RAW LAYER ──
    # Each of the five carrier elements is a NAMED EXPORT and each is a constructor. The list is
    # the library's own enumeration, so the quantifier and the surface move together.
    test-the-five-carrier-elements-are-named-exports = {
      expr = builtins.all (n: v ? ${n} && builtins.isFunction v.${n}) v.carrierElements;
      expected = true;
    };

    test-the-carrier-enumeration-is-the-five = {
      expr = v.carrierElements;
      expected = [
        "edgeLabels"
        "labelWellFormedness"
        "labelOrder"
        "dataOrder"
        "relations"
      ];
    };

    # ★ THE CONTROL THAT THE ENUMERATION IS NOT SELF-SATISFYING. A list of names that happened to
    # be wrong would still pass the cell above if the names it held all existed for other reasons;
    # this one fails on a name that is NOT an export, in the same run and through the same
    # predicate.
    test-control-the-named-export-check-discriminates = {
      expr = builtins.all (n: v ? ${n} && builtins.isFunction v.${n}) (
        v.carrierElements ++ [ "materialize" ]
      );
      expected = false;
    };

    # ── THE COMPOSED LAYER ──
    test-the-named-compositions = {
      expr = builtins.attrNames v.compositions;
      expected = [
        "channel"
        "movement"
        "registry"
        "role"
        "topology"
      ];
    };

    # ── THE CONSTRUCT FAMILIES THAT ARE NOT DECLARATION FIELDS ──
    test-placement-is-a-family-beside-the-declaration = {
      expr = builtins.attrNames v.placement;
      expected = [
        "modes"
        "pathKey"
        "place"
        "setAttrByPath"
        "sourceKey"
        "targetKey"
        "targets"
      ];
    };

    test-content-transformation-is-a-family-beside-the-declaration = {
      expr = builtins.attrNames v.transform;
      expected = [
        "map"
        "over"
        "scan"
      ];
    };

    # ★ NO IDENTIFIER HERE IS NAMED `materialize`. The act between a view definition and a view
    # relation has no term at any held primary — measured zero occurrences of `materializ*` across
    # both corpora, controls live — and it appears only in agent-authored summaries, which are not
    # primaries. The two NAMED THINGS are enough: the declaration and the result, both of which
    # resolve at Manchanda & Warren printed 381. This cell is what keeps the gap from being closed
    # by habit.
    test-no-published-identifier-names-the-unacquired-act = {
      expr = builtins.filter (n: n == "materialize" || n == "materialized") (
        builtins.attrNames v ++ builtins.attrNames v.placement ++ builtins.attrNames v.transform
      );
      expected = [ ];
    };
  };
}
