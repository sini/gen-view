# CONTENT TRANSFORMATION — a SEPARATE CONSTRUCT FAMILY, never declaration fields.
#
# ★★ THE SEPARATION IS FORCED, NOT STYLISTIC. Content transformation is excluded from a view
# definition by construction, because folding it in would reconstruct the released edge grammar
# under new names. But the three operators still have to LAND SOMEWHERE — nothing is dropped for
# want of callers, since a caller count answers "is anything calling it" and never "what does it
# do and is that function covered", and those two questions come apart precisely at instruments,
# which have no callers by construction. So they land here, beside the declaration rather than
# inside it.
#
# ★★ `over` IS THE ONE THAT CAN REORDER, AND ITS REORDER IS MADE VISIBLE RATHER THAN LEFT
# IMPLICIT. It is the only declared place a reorder was ever visible in the surface these three
# come from, so letting it disappear silently would be a loss the ordering law can see. Every
# `over` result carries `reordered` stating whether the sequence it returned is the sequence it was
# given — measured, not promised.
#
# ★ EACH OPERATOR PRODUCES A NEW NAMED RESULT. That is what makes them composable at all: the
# nearest live per-item projections in the ecosystem are a fold's `valueOf` and a reach-fold's
# `project`, and neither is a composable operator producing a new named result — which is exactly
# why neither is a successor to these.
#
# THE FOLD IS RE-RUN, NEVER PATCHED. A transformed result's value is folded from its own
# contributions with the definition's declared combine and unit; carrying the original value
# forward would make the result's `value` disagree with its own `contributions`, and nothing in the
# result would say which was authoritative.
{ prelude }:
let
  inherit (prelude) foldl' map length;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal) refuse fields;

  refold =
    r: name: contributions:
    r
    // {
      inherit name contributions;
      value = foldl' r.definition.combine.op r.definition.empty (map (c: c.datum) contributions);
    };

  named =
    site: value:
    if builtins.isString value && value != "" then
      value
    else
      refuse site "field 'name' must be the non-empty name of the result this operator produces; an operator that renamed nothing would return a second value under the first one's name";

  viewIn =
    site: value:
    if builtins.isAttrs value && (value.__element or null) == "viewRelation" then
      value
    else
      refuse site "field 'relation' must be a materialized view relation; these operators produce a new NAMED RESULT from an existing one, and a definition has no contributions to transform yet";

  # `map { relation; name; f; }` — per-item content projection. `f` sees the whole contribution and
  # returns the new DATUM, so a projection may read the position it is at without being handed a
  # separate position argument.
  mapDatums =
    args:
    let
      a = fields "map" [
        "relation"
        "name"
        "f"
      ] args;
      r = viewIn "map" a.relation;
      name = named "map" a.name;
    in
    if !(builtins.isFunction a.f) then
      refuse "map" "field 'f' must be a function from a contribution to its new datum"
    else
      refold r name (map (c: c // { datum = a.f c; }) r.contributions);

  # `scan { relation; name; f; empty; }` — the PREFIX SCAN. Measured absent from every candidate
  # successor library and from the utility base, which is why it is built rather than pointed at.
  # Each contribution's datum becomes the running accumulation UP TO AND INCLUDING itself, so the
  # last element of a scan equals the fold of the same sequence.
  scan =
    args:
    let
      a = fields "scan" [
        "relation"
        "name"
        "f"
        "empty"
      ] args;
      r = viewIn "scan" a.relation;
      name = named "scan" a.name;
      stepped =
        (foldl'
          (acc: c: {
            state = a.f acc.state c;
            out = acc.out ++ [ (c // { datum = a.f acc.state c; }) ];
          })
          {
            state = a.empty;
            out = [ ];
          }
          r.contributions
        ).out;
    in
    if !(builtins.isFunction a.f) then
      refuse "scan" "field 'f' must be a binary step `accumulator → contribution → accumulator`"
    else
      refold r name stepped;

  # `over { relation; name; f; }` — the unstructured whole-sequence rewrite: sort, take, reverse,
  # cross-element. `f : [ contribution ] → [ contribution ]`.
  over =
    args:
    let
      a = fields "over" [
        "relation"
        "name"
        "f"
      ] args;
      r = viewIn "over" a.relation;
      name = named "over" a.name;
      out = a.f r.contributions;
    in
    if !(builtins.isFunction a.f) then
      refuse "over" "field 'f' must be a function from the contribution sequence to a new sequence"
    else if !(builtins.isList out) then
      refuse "over" "the rewrite returned a ${builtins.typeOf out}; `over` produces a contribution SEQUENCE, and a result that is not one cannot be folded or traced"
    else
      (refold r name out)
      // {
        # ★ MEASURED, NOT PROMISED. A rewrite that returns the sequence unchanged says so; one that
        # reorders or resizes says that instead, and a consumer whose ordering law cares can read
        # it rather than re-derive it.
        reordered = out != r.contributions;
        resized = length out != length r.contributions;
      };
in
{
  inherit
    mapDatums
    scan
    over
    refold
    ;
}
