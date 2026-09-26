# PLACEMENT — the construct family that says WHERE a named result lands, kept deliberately OUT of
# the view definition.
#
# ★★ WHY IT IS A SEPARATE FAMILY AND NOT A SET OF DECLARATION FIELDS. Folding placement, the
# terminal sink and content transformation into the declaration would RECONSTRUCT THE RELEASED
# EDGE GRAMMAR — its (source, target, path, mode) tuple — under new names, and that grammar was
# released rather than renamed. Keeping them here gives the four homeless constructs a home
# without giving the declaration a shape a ruling took away from it.
#
# The four that landed here, each named in the record that left them homeless: the three PLACEMENT
# MODES with DEDUP EXEMPTION AS A PLACEMENT PROPERTY, `setAttrByPath`, the TERMINAL SINK
# (`targets.output`), and mutate-with-a-position. Three of the four are still here; the fourth
# retired to gen-prelude and the reversal is recorded next.
#
# ★ `setAttrByPath` WAS PUBLISHED FROM HERE AND THE OWNER RULED THE OTHER WAY (2026-08-27). The
# position this file took, kept verbatim in substance because a rejected position that leaves no
# trace gets re-proposed: the primitive was MEASURED absent from every candidate successor library
# AND from the utility base, while three private twins of it existed in the ecosystem — the exact
# shape of a raw primitive trapped inside composition-only libraries, which is the failure the
# raw-calculus rule exists to prevent. The gen libraries are nixpkgs-lib-free, so the ambient
# implementation was not an available substitute. Deferring to a consolidated library that did not
# yet exist was therefore DECLINED, and publishing from here was chosen over waiting.
#
# THE REVERSAL, and why the declined position does not survive it: that measurement was of an
# ABSENCE in the utility base, and the ruling FILLED the absence rather than leaving it — the pair
# `setAttrByPath` + `getAttrByPath` landed in gen-prelude (`a2d2e7d`, `a05779b`), which is the
# named owner a primitive wants and which this library never was. So the export is withdrawn and
# the internal use below consumes `prelude.setAttrByPath`. What the raw-calculus rule bought here
# still holds: the primitive is published, just not from a placement library. Placement keeps the
# CONSTRUCT and stops keeping the PRIMITIVE.
#
# ★ THE ORDERING COUPLING, RECORDED BECAUSE IT DECIDES A RETIREMENT SEQUENCE: the sort key
# of the oracle cluster (`trace.nix`) keys on the PATH and the MODE, both of which are components
# of this family. The key therefore cannot be re-expressed until placement has a home, which
# is here — so this file is upstream of that cluster's retirement, not beside it.
{ prelude }:
let
  inherit (prelude) elem setAttrByPath;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    decided
    choice
    strings
    attrKey
    tupleKey
    quote
    renderValue
    ;

  modes = [
    "merge"
    "nest"
    "nest-verbatim"
  ];

  # `rootNames site target` — THE ONE CHECK ON A ROOT TARGET'S TWO NAMES, returning the target
  # unchanged so it is a pass-through and cannot be written and not called. Every consumer of a root
  # target interpolates `scope` and `channel` (`targetKey`, `writesOf`'s cell, `edgeSortKey` through
  # `targetKey`), and interpolation aborts past `tryEval` on anything that is not a string, so an
  # ill-typed name is refused here by name instead.
  #
  # ★ IT RUNS AT CONSTRUCTION AND AGAIN AT EACH CONSUMER'S ROOT ARM, because an element tag is a
  # CLAIM and not a proof: a hand-built record carrying `__element = "target"` reaches a consumer
  # without passing `targets.root`, and it is owed the same named refusal. One definition, so the
  # sites cannot drift apart.
  #
  # ★ THE CHECK IS THE WHNF OF THE RESULT, never a field of it. A per-field check inside the record
  # would defer until the field is read, and an intake testing only the tag would not force it, so
  # a consumer would accept the element and meet the abort later.
  rootNames =
    site: target:
    if !(builtins.isString target.scope) || target.scope == "" then
      refuse site "field 'scope' is ${renderValue target.scope}; it must be a non-empty scope id, the root the result lands at"
    else if !(builtins.isString target.channel) || target.channel == "" then
      refuse site "field 'channel' is ${renderValue target.channel}; it must be a non-empty channel name, the cell the result lands in"
    else
      target;

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
      rootNames "targets.root" {
        __element = "target";
        arm = "root";
        inherit (a) scope channel;
      };
    output =
      args:
      let
        a = fields "targets.output" [ "path" ] args;
        path = strings "targets.output" "path" a.path;
      in
      decided [ path ] {
        __element = "target";
        arm = "output";
        inherit path;
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
      decided [ mode path ] {
        __element = "placement";
        inherit mode path;
        inherit (a) name value;
        # The verbatim arm is the one exempt from dedup: its content is placed as written.
        dedupExempt = mode == "nest-verbatim";
        # `merge` joins the bucket AT the path; both nesting arms place the result UNDER its own
        # name. That is the whole observable difference between the two families, and it is one
        # expression rather than three.
        #
        # ★ AN INTENTIONAL DIVERGENCE FROM den v1, RECORDED RATHER THAN LEFT TACIT. Both nesting arms
        # write `path ++ [ name ]`; the predecessor's placement wrote exactly `path`, with no name
        # segment appended, for every arm it had. This is the designed semantics for this construct
        # family, not an unresolved gap: distinct named contributions stay distinct under one path,
        # which the ADR-0010 edge grammar's mode component (`M` of `(S,T,P,M)`) exists to select
        # between. The predecessor's exact-at-P shape is still expressible here — it is the `merge`
        # arm above — and a caller migrating a v1-shaped tree maps onto it through the adapter/lens
        # ADR-0027 assigns that role, not through a fourth mode here.
        placed =
          if mode == "merge" then
            setAttrByPath (map attrKey path) a.value
          else
            setAttrByPath (map attrKey (path ++ [ a.name ])) a.value;
      };

  # `pathKey` / `targetKey` / `sourceKey` — the components the sort key is built from, each the JSON
  # of its name tuple (`tupleKey`), so distinct names give distinct components by construction.
  # Published because the key is built from them and a caller re-deriving one by hand would be
  # re-deriving the encoding. The arm tag and the shape at position 1 (a string for a root's scope,
  # a list for an output's path) keep the two target arms apart.
  pathKey = path: tupleKey "pathKey" null path;
  targetKey =
    target:
    if target.arm == "output" then
      tupleKey "targetKey" 1 [
        "out"
        target.path
      ]
    else
      let
        t = rootNames "targetKey" target;
      in
      tupleKey "targetKey" null [
        "root"
        t.scope
        t.channel
      ];
  # ★ JSON-ENCODED BUT NOT GUARDED: interpolation keeps exactly today's admission — a non-string
  # still aborts, an `outPath`/`__toString` set still coerces — because the raw trace surface's
  # coercion class is an open owner reading (`den-hoag-g1qy0`) that a guard here would pre-empt. A
  # bare `toJSON` would be worse than either: it silently keys an int, a plain set, a list or null.
  sourceKey =
    source:
    builtins.toJSON [
      "${source.scope}"
      "${source.relation}"
    ];
in
{
  inherit
    modes
    targets
    place
    pathKey
    targetKey
    sourceKey
    rootNames
    ;
}
