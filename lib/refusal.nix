# NAMED REFUSALS — the single construction every field check in this library goes through.
#
# EVERY OMITTED FIELD YIELDS A REFUSAL NAMING THE FIELD, and a read against an undeclared name is
# refused by name. The measured precedent this exists to forbid is gen-resolve's shipped grammar,
# where a misspelled channel silently yields `{ }` and the undeclared-channel check reads `false`
# even under `deepSeq` — an empty answer standing in for a refusal, which no caller can tell from
# a channel that legitimately gathered nothing.
#
# ★ AN EMPTY ANSWER IS NEVER A REFUSAL, which is why every arm here THROWS rather than returning a
# sentinel. A sentinel is a value: a caller that forgets to look at it has an answer, and the
# failure re-enters the program one layer down wearing the shape of data.
#
# ★★ ABSENCE IS A DECISION, SO THE CHECK IS TWO-SIDED. `missing` catches an omitted field;
# `unknown` catches a field nobody declared — a misspelling that would otherwise leave the real
# field missing AND leave the caller's intent nowhere. Both directions name what they found. A
# defaulted field would make either failure silent, which is why this library defaults nothing:
# a default is a decision nobody made and nobody can see.
{ prelude }:
let
  inherit (prelude)
    filter
    elem
    groupBy
    head
    length
    sort
    attrNames
    concatStringsSep
    ;

  # The refusal itself. One prefix, so every message in the library is greppable to its site and
  # a consumer's error names the construct that refused rather than the file it lives in.
  refuse = site: message: throw "gen-view.${site}: ${message}";

  # TOTAL RENDERING OF A CALLER VALUE INSIDE A REFUSAL — the shape of gen-scope's `renderValue`
  # (`lib/cascade.nix`). A refusal is built at the moment something has already gone wrong, and it
  # renders exactly the value that was wrong: `toJSON` aborts on a function at any depth and
  # overflows on a cyclic value, and string interpolation aborts on anything that is not a string,
  # all three past `tryEval`. Scalars and name lists render in full, because those are the shapes a
  # caller acts on; anything else is named by its type. It forces the value, and a list's elements,
  # to WHNF and no further, so a cyclic value renders; an element whose own evaluation diverges or
  # throws still does so here, as it would under any render. It RENDERS and never ADDRESSES: two
  # different lambdas render alike, which a message may do and a key may not.
  renderValue =
    v:
    if builtins.isString v || builtins.isInt v || builtins.isBool v || v == null then
      builtins.toJSON v
    else if builtins.isList v && builtins.all builtins.isString v then
      builtins.toJSON v
    else
      "<a ${builtins.typeOf v}>";

  # A name renders quoted as a name, and anything else through `renderValue`.
  renderSubject = v: if builtins.isString v then "'${v}'" else renderValue v;

  # A list of names in the order a refusal reports from. `lessThan` aborts past `tryEval` on two
  # values it cannot compare (two lambdas, a lambda and a string), so a list that is not all
  # strings keeps its position order: the same elements, and the one to report is still named.
  sortNames = xs: if builtins.all builtins.isString xs then sort builtins.lessThan xs else xs;

  quote =
    names:
    if builtins.isList names && builtins.all builtins.isString names then
      concatStringsSep ", " (sort builtins.lessThan names)
    else
      renderValue names;

  # `decided checks value` — every check in `checks` forced to WHNF before `value` is returned, so a
  # constructor's field checks are decided where the element is BUILT, never where a field is first
  # READ. Each check is a pass-through (`strings`, `choice`, `elementOf`, `materialized`, `named`)
  # whose WHNF is its verdict. A check bound in a `let` and only inherited into the record would run
  # when the field is read, and an intake testing only the tag would not force it, so a consumer
  # would accept the element and meet the refusal, or an abort, later. The same rule as `rootNames`
  # in placement.nix.
  #
  # ★ THE TRADE-OFF. Checks are forced; content is not: a datum, `place.value`, `scan.empty`, an
  # edge accessor's or `wellFormed`'s result stay lazy. But a decided FIELD is no longer lazy: a
  # throwing or diverging value there fails at construction even when no consumer ever reads that
  # field. The cost is the forced check's own work, once per element: O(1) for `choice`, O(n) for a
  # `strings` list, and for `elementOf` whatever the forced element's own chain costs — so reading
  # only a `viewRelation`'s `name` now pays its graph's check, about ten calls per graph entry.
  decided = checks: value: builtins.seq (builtins.all (c: builtins.seq c true) checks) value;

  # `returned site role contract ok v` — the RESULT of a caller-supplied function, checked where it
  # is consumed, which is the only place it exists. `decided`'s rule one level down: the check's
  # WHNF is its verdict and it hands back `v` itself, so the consumer reads the checked value and
  # the check cannot be written and not called. It forces `v` to WHNF and runs `ok`, nothing more,
  # so a result's CONTENT stays as lazy as the consumer leaves it. `role` names the function and
  # the input it was applied to; `renderValue` names what it returned.
  returned =
    site: role: contract: ok: v:
    if ok v then v else refuse site "${role} returned ${renderValue v}; ${contract}";

  # `formalsOf v` — the formals a function destructures (`{ x }: …` has `[ "x" ]`), `[ ]` for a
  # plain lambda or a non-function. Where a construct applies `v` to a STRING, a non-empty list
  # means `v` can never be applied, and the site refuses that by name before the application
  # aborts past `tryEval`. It refuses only a value that can satisfy NO APPLICATION of its contract;
  # the door sits at construction, so such a value is refused even on a read that never applies it
  # (as the `nonAccessor` door already refuses a non-function there). Sound, not complete:
  # `{ ... }:` and `{ }:` report no formals and still abort, and `formalsOf` is `[ ]` for every
  # functor, so a functor whose `__functor` destructures passes; those are pinned as falsifier cells.
  formalsOf = v: if builtins.isFunction v then builtins.attrNames (builtins.functionArgs v) else [ ];

  # `fields site required args` — `required` present in `args`, and nothing else present at all.
  # Returns `args` on success so the check is a pass-through and cannot be written and not called.
  fields =
    site: required: args:
    let
      given = attrNames args;
      missing = filter (f: !(builtins.hasAttr f args)) required;
      unknown = filter (f: !(elem f required)) given;
    in
    # `attrNames` and `hasAttr` abort past `tryEval` on anything that is not an attrset, so the
    # argument's own type is refused by name before either is forced.
    if !(builtins.isAttrs args) then
      refuse site "the argument must be an attrset of this construct's fields, not a ${builtins.typeOf args} (required: ${quote required})"
    else if missing != [ ] then
      refuse site "required field '${head (sort builtins.lessThan missing)}' is not declared; every field of this construct is required and total (declared: ${quote given}; required: ${quote required})"
    else if unknown != [ ] then
      refuse site "field '${head (sort builtins.lessThan unknown)}' is not a field of this construct; the field set is closed (required: ${quote required})"
    else
      args;

  # `choice site field allowed value` — a closed enumeration, refused BY NAME with its arms named.
  # The arms are quoted in the message because a caller who guessed wrong needs the set, not the
  # verdict: a refusal that only denies sends the reader to the source to find out what is legal.
  choice =
    site: field: allowed: value:
    if elem value allowed then
      value
    else
      refuse site "field '${field}' is ${renderValue value}, which is not one of the declared arms (${quote allowed})";

  # `attrKey k` — the attribute name a caller-supplied identifier is KEYED under: its text, with
  # string context discarded from the key only. An attribute name cannot carry context, and `==`
  # and `strings`' duplicate check below both ignore it, so the text is exactly what a key can hold
  # (gen-prelude `unique`'s keying). The caller's value is never replaced. A non-string passes
  # through unchanged, because the discard COERCES an `outPath`/`__toString` set or a path and
  # would silently admit it as a name.
  attrKey = k: if builtins.isString k then builtins.unsafeDiscardStringContext k else k;

  # `tupleKey site pathAt components` — the key of a tuple of caller names: the JSON of the
  # component list. A JSON string literal escapes `"` and `\`, so each component ends at its first
  # unescaped quote and a list of them parses one way only: distinct tuples give distinct keys BY
  # CONSTRUCTION, where a separator join lets a name carrying the separator shift the boundaries.
  # `lib/relation.nix` keys its groupings the same way (`elementKeyOf`).
  #
  # ★ THE GUARD IS POSITION-AWARE, because the shapes are what keep the arms apart: every component
  # is a string except the one at `pathAt` (`null` where the tuple has no path), which is a list of
  # strings. A guard admitting either shape anywhere would key `cell "out" [ "x/y" ] "output"` equal
  # to the output arm's `[ "out" [ "x/y" ] "output" ]`. It refuses by name before `toJSON`, which
  # would otherwise coerce an `outPath` set to its string, or silently key an int or a plain set.
  tupleKey =
    site: pathAt: components:
    let
      ok =
        i: c:
        if i == pathAt then builtins.isList c && builtins.all builtins.isString c else builtins.isString c;
      bad = filter (i: !(ok i (builtins.elemAt components i))) (
        builtins.genList (i: i) (length components)
      );
      i = head bad;
    in
    if !(builtins.isList components) then
      refuse site "a key is a list of components, not a ${builtins.typeOf components}"
    else if bad != [ ] then
      refuse site "a key component is ${renderValue (builtins.elemAt components i)}; ${
        if i == pathAt then
          "a path in a key must be a list of strings"
        else
          "a name in a key must be a string"
      }"
    else
      builtins.toJSON components;

  # `strings site what xs` — a list of distinct non-empty strings, the shape every alphabet and
  # name set in the carrier takes. Duplicates are refused rather than collapsed: a set written
  # twice is a caller who believes two things about it, and silently deduplicating picks one.
  # `counts` keys by the context-discarded text, as gen-prelude `unique` does: `==` ignores string
  # context, so two copies differing only in context are a duplicate, and `groupBy` aborts on a
  # context-carrying key.
  strings =
    site: what: xs:
    let
      bad = filter (x: !(builtins.isString x)) xs;
      empties = filter (x: x == "") xs;
      counts = groupBy builtins.unsafeDiscardStringContext xs;
      dups = filter (k: length counts.${k} > 1) (attrNames counts);
    in
    if !(builtins.isList xs) then
      refuse site "${what} must be a list, not a ${builtins.typeOf xs}"
    else if bad != [ ] then
      refuse site "${what} carries a ${builtins.typeOf (head bad)} where a string is required"
    else if empties != [ ] then
      refuse site "${what} carries the empty string, which names nothing"
    else if dups != [ ] then
      refuse site "${what} names '${head (sort builtins.lessThan dups)}' more than once"
    else
      xs;
in
{
  inherit
    tupleKey
    refuse
    fields
    decided
    returned
    formalsOf
    choice
    strings
    attrKey
    quote
    renderValue
    renderSubject
    sortNames
    ;
}
