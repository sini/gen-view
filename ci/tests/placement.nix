# PLACE()'S NESTING SHAPE — RULED INTENTIONAL, PINNED HERE (2026-09-25 sitting, agenda item 39).
#
# `nest` and `nest-verbatim` place a result under `path ++ [ name ]`; den v1 placed exactly at
# `path`, appending no name, for every arm it had. The reading that flight surfaced was whether
# that is a defect (v1's shape reverts) or gen-view's designed semantics. It is ruled the latter:
# distinct named contributions stay distinct under one path, which is the `M` component the
# ADR-0010 edge grammar `(S,T,P,M)` exists to select between. v1's exact-at-P shape stays
# expressible — it is `merge` — so the pin below plants the "other" (v1) shape as a literal and
# asserts nesting is NOT that, rather than only asserting what nesting IS.
{ genView, ... }:
let
  v = genView;
  value = [ "x" ];
  placeAt =
    mode:
    v.placement.place {
      inherit mode;
      path = [ "box" ];
      name = "widget";
      inherit value;
    };
  # v1's shape for the same call: exactly at `path`, no name segment. Written out rather than
  # derived from `merge`, so a defect that broke `merge` could not make this control vacuous.
  exactAtPath = {
    box = value;
  };
in
{
  flake.tests.placement = {
    test-nest-places-the-value-under-its-own-name = {
      expr = (placeAt "nest").placed;
      expected = {
        box = {
          widget = value;
        };
      };
    };
    test-nest-verbatim-places-the-value-under-its-own-name-too = {
      expr = (placeAt "nest-verbatim").placed;
      expected = {
        box = {
          widget = value;
        };
      };
    };
    # THE PLANTED-OTHER-BEHAVIOUR CONTROL: den v1's exact-at-P shape is a real value, not a stand-in
    # that could never match, and both nesting arms must disagree with it.
    test-control-nest-does-not-place-exactly-at-path-like-v1 = {
      expr = (placeAt "nest").placed == exactAtPath;
      expected = false;
    };
    test-control-nest-verbatim-does-not-place-exactly-at-path-like-v1 = {
      expr = (placeAt "nest-verbatim").placed == exactAtPath;
      expected = false;
    };
    # v1's shape is not withdrawn, it is `merge` — this is where a caller migrating a v1-shaped
    # tree lands, and the cell that would notice if `merge` drifted away from it.
    test-merge-still-places-exactly-at-path-like-v1 = {
      expr = (placeAt "merge").placed;
      expected = exactAtPath;
    };
  };
}
