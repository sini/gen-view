# PLACEMENT — the construct family that says WHERE a named result lands, kept deliberately OUT of
# the view definition.
#
# ★★ WHY IT IS A SEPARATE FAMILY AND NOT A SET OF DECLARATION FIELDS. Folding placement, the
# terminal sink and content transformation into the declaration would RECONSTRUCT THE RELEASED
# EDGE GRAMMAR — its (source, target, path, mode) tuple — under new names, and that grammar was
# released rather than renamed. Keeping them here gives the four homeless constructs a home
# without giving the declaration a shape a ruling took away from it.
#
# The four that land here, each named in the record that left them homeless: the three PLACEMENT
# MODES with DEDUP EXEMPTION AS A PLACEMENT PROPERTY, `setAttrByPath`, the TERMINAL SINK
# (`targets.output`), and mutate-with-a-position.
#
# ★ `setAttrByPath` IS PUBLISHED, AND THAT IS THE POINT OF PUBLISHING IT. It was measured absent
# from every candidate successor library AND from the utility base, while three private twins of it
# exist in the ecosystem — the exact shape of a raw primitive trapped inside composition-only
# libraries, which is the failure the raw-calculus rule exists to prevent. The gen libraries are
# nixpkgs-lib-free, so the ambient implementation is not an available substitute.
#
# ★ THE ORDERING COUPLING, RECORDED BECAUSE IT DECIDES A RETIREMENT SEQUENCE: the frozen sort key
# of the oracle cluster (`trace.nix`) keys on the PATH and the MODE, both of which are components
# of this family. The frozen key therefore cannot be re-expressed until placement has a home, which
# is here — so this file is upstream of that cluster's retirement, not beside it.
{ prelude }:
let
  inherit (prelude) foldl' elem;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    choice
    strings
    quote
    ;

  modes = [
    "merge"
    "nest"
    "nest-verbatim"
  ];

  # `setAttrByPath [ "a" "b" ] v` ⇒ `{ a.b = v; }`. The empty path is the value itself, which is
  # what makes `place` with a root-level target a plain case rather than a special one.
  setAttrByPath =
    path: value:
    foldl' (acc: seg: { ${seg} = acc; }) value (
      # Right fold via a reversed left fold: the LAST segment is the innermost attribute.
      builtins.genList (i: builtins.elemAt path (builtins.length path - 1 - i)) (builtins.length path)
    );

  # THE TARGETS. Two arms, and the second is the TERMINAL SINK — a position outside the graph
  # entirely, which is why it is an arm of its own rather than a scope that happens to be special.
  targets = {
    root =
      args:
      let
        a = fields "targets.root" [
          "scope"
          "channel"
        ] args;
      in
      {
        __element = "target";
        arm = "root";
        inherit (a) scope channel;
      };
    output =
      args:
      let
        a = fields "targets.output" [ "path" ] args;
      in
      {
        __element = "target";
        arm = "output";
        path = strings "targets.output" "path" a.path;
      };
  };

  # `place { mode; path; name; value; }` — mutate-with-a-position, as a value rather than an act.
  #
  # ★ DEDUP EXEMPTION IS A PLACEMENT PROPERTY AND IS CARRIED AS ONE. The verbatim nesting arm
  # exists precisely because its content must not be collapsed against a structurally equal
  # sibling; expressing that as a flag on the DEDUP policy would put a placement fact in the
  # declaration, which is the fold this family exists to prevent.
  place =
    args:
    let
      a = fields "place" [
        "mode"
        "path"
        "name"
        "value"
      ] args;
      mode = choice "place" "mode" modes a.mode;
      path = strings "place" "path" a.path;
    in
    if !(builtins.isString a.name) || a.name == "" then
      refuse "place" "field 'name' must be the non-empty name of the result being placed"
    else
      {
        __element = "placement";
        inherit mode path;
        inherit (a) name value;
        # The verbatim arm is the one exempt from dedup: its content is placed as written.
        dedupExempt = mode == "nest-verbatim";
        # `merge` joins the bucket AT the path; both nesting arms place the result UNDER its own
        # name. That is the whole observable difference between the two families, and it is one
        # expression rather than three.
        placed =
          if mode == "merge" then setAttrByPath path a.value else setAttrByPath (path ++ [ a.name ]) a.value;
      };

  # `pathKey` / `targetKey` / `sourceKey` — the rendered components the frozen sort key is built
  # from. Published because the key is built from them and a caller re-deriving one by hand would
  # be re-deriving the frozen format.
  pathKey = path: if path == [ ] then "-" else builtins.concatStringsSep "." path;
  targetKey =
    target:
    if target.arm == "output" then
      "out:" + builtins.concatStringsSep "." target.path
    else
      "root:" + target.scope + "/" + target.channel;
  sourceKey = source: source.scope + "/" + source.relation;
in
{
  inherit
    modes
    setAttrByPath
    targets
    place
    pathKey
    targetKey
    sourceKey
    ;
}
