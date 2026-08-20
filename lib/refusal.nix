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
    head
    length
    sort
    attrNames
    concatStringsSep
    ;

  # The refusal itself. One prefix, so every message in the library is greppable to its site and
  # a consumer's error names the construct that refused rather than the file it lives in.
  refuse = site: message: throw "gen-view.${site}: ${message}";

  quote = names: concatStringsSep ", " (sort builtins.lessThan names);

  # `fields site required args` — `required` present in `args`, and nothing else present at all.
  # Returns `args` on success so the check is a pass-through and cannot be written and not called.
  fields =
    site: required: args:
    let
      given = attrNames args;
      missing = filter (f: !(builtins.hasAttr f args)) required;
      unknown = filter (f: !(elem f required)) given;
    in
    if missing != [ ] then
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
      refuse site "field '${field}' is ${builtins.toJSON value}, which is not one of the declared arms (${quote allowed})";

  # `strings site what xs` — a list of distinct non-empty strings, the shape every alphabet and
  # name set in the carrier takes. Duplicates are refused rather than collapsed: a set written
  # twice is a caller who believes two things about it, and silently deduplicating picks one.
  strings =
    site: what: xs:
    let
      bad = filter (x: !(builtins.isString x)) xs;
      empties = filter (x: x == "") xs;
      dups = filter (x: length (filter (y: y == x) xs) > 1) xs;
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
    refuse
    fields
    choice
    strings
    quote
    ;
}
