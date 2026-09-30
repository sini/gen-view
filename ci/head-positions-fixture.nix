# THE HEAD-POSITIONS FIXTURE — ADR-0029's four-tier cases (den-hoag-zakjg, spec §6(iii)/(iv)) driven
# through `headPositions` and `joinedTrace`, read by `ci/tests/head-positions.nix` and by the refusal
# cells in `ci/tests-error.nix`.
#
# Topology: `r` is the query root, `r —tacks→ t` (and `r —tacks→ u` for the tie cells). Each
# contributor is its OWN module evaluation of `x : str, default = "RD"`, with a `_file` naming it, so
# a record's `winners` names its contributor and a mis-keyed join is visible.
#
# ★ THE RECORDS ARE A PROTOTYPE OF THE BAND READ'S CONTRACT (spec §8 U1), NOT THE UNIT. The band
# thresholds are the owner's ruling (< 100, < 1000, < 1500, else not moved), read off the nixpkgs
# module system's `highestPrio`: nixpkgs is a ci-only dependency here, on the terms `flake.nix`
# states, and the library under test never sees it. `innerOf` is opaque to the library, so what
# these cells pin is the join's door and its reading of the trace, not the band read itself.
{ genView, lib }:
let
  v = genView;
  heads = [
    "force"
    "set"
    "default"
  ];

  bandOf =
    p:
    if p < 100 then
      "force"
    else if p < 1000 then
      "set"
    else if p < 1500 then
      "default"
    else
      null;
  optDecl = {
    options.x = lib.mkOption {
      type = lib.types.str;
      default = "RD";
    };
  };
  recordOf =
    scope: defs:
    let
      ev = lib.evalModules {
        modules = [
          optDecl
        ]
        ++ map (d: {
          _file = "${scope}.nix";
          config.x = d;
        }) defs;
      };
      o = ev.options.x;
      band = bandOf o.highestPrio;
    in
    {
      inherit scope;
      loc = [ "x" ];
      priority = o.highestPrio;
    }
    // (
      if band == null then
        { reason = "unset: default-only"; }
      else
        {
          inherit band;
          value = ev.config.x;
          winners = map (d: d.file) o.definitionsWithLocations;
        }
    );
  # THE RECEIVER (spec §8 U4, gate C2): an evaluation whose definitions of the field are exactly
  # the moved list, seeded by its own declared default.
  receiver =
    moved: (lib.evalModules { modules = [ optDecl ] ++ map (d: { config.x = d; }) moved; }).config.x;

  structure =
    {
      endOfPath ? -1,
      scopes ? [
        "r"
        "t"
      ],
      letters ? [ "tacks" ],
      expression ? "tacks?",
      edges ? {
        tacks = id: if id == "r" then builtins.filter (s: s != "r") scopes else [ ];
      },
    }:
    let
      labels = v.edgeLabels { inherit letters; };
    in
    v.scopeGraph {
      carrier = v.carrier {
        inherit labels;
        relations = v.relations { names = [ "gimp" ]; };
        relatumLabels = v.relatumLabels { names = [ ]; };
        labelWellFormedness = v.labelWellFormedness {
          alphabet = labels;
          inherit expression;
        };
        # `$` before every letter: the root's own shorter word beats one continuing on `tacks`,
        # "most specific wins". `endOfPath = 1` is the mutant where continuing beats stopping.
        labelOrder = v.labelOrder {
          alphabet = labels;
          layers = [ letters ];
          inherit endOfPath;
        };
        dataOrder = v.dataOrder {
          channel = "selvage";
          keyOf = _: "selvage";
        };
      };
      inherit scopes edges;
      data = [ ];
    };

  placed =
    records:
    lib.concatMap (
      r:
      lib.optional (r ? band) {
        inherit (r) scope;
        head = r.band;
        relation = "gimp";
        datum = [ r.value ];
      }
    ) records;

  positionsOf =
    {
      endOfPath ? -1,
      scopes ? [
        "r"
        "t"
      ],
    }:
    data:
    v.headPositions {
      inherit heads data;
      structure = structure { inherit endOfPath scopes; };
      root = "r";
    };

  relationOver =
    pos:
    {
      tieSet ? v.tieSets.union,
      root ? pos.root,
      wellFormed ? _: true,
    }:
    v.viewRelation {
      definition = v.compositions.movement {
        channel = "selvage";
        relation = "gimp";
        inherit (pos) admission order;
        inherit root wellFormed;
        direction = "outbound";
        empty = [ ];
        inherit tieSet;
        combine = v.combines.listAppend;
        dedup = v.dedups.none;
      };
      marks = _: [ ];
      inherit (pos) orderMark graph;
    };

  cases = {
    k1 = {
      r = [ "R" ];
      t = [ "T" ];
    };
    k2 = {
      r = [ (lib.mkDefault "RD") ];
      t = [ "T" ];
    };
    k3 = {
      r = [ ];
      t = [ (lib.mkDefault "TD") ];
    };
    k4 = {
      r = [ "R" ];
      t = [ (lib.mkForce "TF") ];
    };
    k5 = {
      r = [ (lib.mkOptionDefault "RO") ];
      t = [ ];
    };
    k6 = {
      r = [ ];
      t = [ ];
    };
  };
  recordsOf = k: lib.mapAttrs recordOf cases.${k};

  # One case, end to end. `innerOf` defaults to the right one; `swapped` joins each contributor to
  # the other's record, the mis-keyed arm. `unplaced` names scopes whose moved datum is withheld
  # from `data`; `root` picks the relation's root from the positions; `wellFormed` is the WFD.
  run =
    {
      endOfPath ? -1,
      innerOf ? null,
      unplaced ? [ ],
      root ? pos: pos.root,
      wellFormed ? _: true,
    }:
    k:
    let
      rs = recordsOf k;
      pos = positionsOf { inherit endOfPath; } (
        placed (builtins.filter (r: !(builtins.elem r.scope unplaced)) (builtins.attrValues rs))
      );
      vr = relationOver pos {
        root = root pos;
        inherit wellFormed;
      };
      joined = v.joinedTrace {
        relation = vr;
        placement = {
          mode = "merge";
          path = [ ];
        };
        positions = pos;
        innerOf = if innerOf == null then s: rs.${s} else innerOf rs;
      };
      mentions =
        s:
        builtins.any (x: pos.owners.${x.scope}.scope == s) (vr.contributions ++ vr.shadowed ++ vr.withheld);
    in
    {
      inherit
        rs
        pos
        vr
        joined
        ;
      moved = vr.value;
      received = receiver vr.value;
      substrateMentions = {
        r = mentions "r";
        t = mentions "t";
      };
    };
  swapped =
    rs: s:
    rs.${
      {
        r = "t";
        t = "r";
      }
      .${s}
    };

  # three contributors, all setting at one structural distance except the root: a within-head tie
  tie =
    tieSet:
    let
      pos =
        positionsOf
          {
            scopes = [
              "r"
              "t"
              "u"
            ];
          }
          (placed [
            (recordOf "t" [ "T" ])
            (recordOf "u" [ "U" ])
          ]);
    in
    (relationOver pos { tieSet = tieSet pos; }).value;

  # Q3: the root sets "R"; the other contributor's authority is a raw `mkForce "TF"` written as its
  # DATUM and placed under the caller-declared head `set`. The door files it by its head letter and
  # never reads the value, so the marker is data and loses to `r` within the one head.
  q3InValue =
    let
      pos = positionsOf { } [
        {
          scope = "r";
          head = "set";
          relation = "gimp";
          datum = [ "R" ];
        }
        {
          scope = "t";
          head = "set";
          relation = "gimp";
          datum = [ (lib.mkForce "TF") ];
        }
      ];
      vr = relationOver pos { };
    in
    {
      moved = map (x: x._type or x) vr.value;
      received = receiver vr.value;
      shadowed = map (s: pos.owners.${s.scope}.scope) vr.shadowed;
      shadowedDatumTypes = map (s: (builtins.head s.datum)._type or "none") vr.shadowed;
    };
in
{
  inherit
    v
    heads
    structure
    positionsOf
    relationOver
    placed
    recordOf
    run
    swapped
    tie
    q3InValue
    ;
}
