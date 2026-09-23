# ── A KEY OVER CALLER NAMES IS INJECTIVE BY CONSTRUCTION ──
# Every composite key gen-view builds from caller names — a target, a source, a path, a cell, a
# write — is the JSON of its component list. Under the separator joins it replaced, a name carrying
# the separator shifted the field boundaries and two distinct tuples rendered one key. Each pair
# below collided that way, and the schedule pair was REFUSED as a cycle it does not have: `cell` is
# the join key of the flow-dependence relation, so a collision there changes an answer, not a label.
{ genView, ... }:
let
  v = genView;
  f = import ../fixture.nix { inherit genView; };
  root =
    s: c:
    v.placement.targets.root {
      scope = s;
      channel = c;
    };
  out = p: v.placement.targets.output { path = p; };
  g = v.scopeGraph {
    inherit (f) carrier;
    scopes = [
      "a/b"
      "x"
      "x/b"
      "q"
    ];
    edges = {
      parent = _: [ ];
      include = _: [ ];
    };
    data = [
      {
        scope = "a/b";
        relation = "import";
        datum = [ "ab" ];
      }
      {
        scope = "x";
        relation = "import";
        datum = [ "x" ];
      }
      {
        scope = "q";
        relation = "import";
        datum = [ "q" ];
      }
    ];
  };
  rel =
    r: c:
    f.mkRelation {
      graph = g;
      definition = f.mkDefinition {
        root = r;
        channel = c;
      };
    };
  order =
    u:
    let
      t = builtins.tryEval (
        builtins.deepSeq (v.accumulatorOrder { units = u; }) (v.accumulatorOrder { units = u; })
      );
    in
    if t.success then t.value else "REFUSED";
  w =
    t:
    v.writesOf {
      relation = rel "q" "y";
      target = t;
      mode = "merge";
    };
in
{
  flake.tests.key-encoding = {
    test-a-root-target-scope-carrying-the-separator-keys-apart = {
      expr = v.placement.targetKey (root "a/b" "c") == v.placement.targetKey (root "a" "b/c");
      expected = false;
    };
    test-an-output-path-with-a-dotted-segment-keys-apart-from-two-segments = {
      expr =
        v.placement.targetKey (out [ "a.b" ]) == v.placement.targetKey (out [
          "a"
          "b"
        ]);
      expected = false;
    };
    test-a-source-scope-carrying-the-separator-keys-apart = {
      expr =
        v.placement.sourceKey {
          scope = "a/b";
          relation = "c";
        } == v.placement.sourceKey {
          scope = "a";
          relation = "b/c";
        };
      expected = false;
    };
    test-a-path-key-separates-a-dotted-segment-and-the-empty-path = {
      expr = {
        dot =
          v.placement.pathKey [ "a.b" ] == v.placement.pathKey [
            "a"
            "b"
          ];
        sentinel = v.placement.pathKey [ ] == v.placement.pathKey [ "-" ];
      };
      expected = {
        dot = false;
        sentinel = false;
      };
    };
    test-a-cell-scope-carrying-the-separator-keys-apart = {
      expr = v.cell "a/b" "c" "input" == v.cell "a" "b/c" "input";
      expected = false;
    };
    test-an-output-write-keys-apart-from-a-root-write-and-a-dotted-path = {
      expr = {
        crossArm = w (root "out:x" "y") == w (out [ "x/y" ]);
        dotted =
          w (out [ "a.b" ]) == w (out [
            "a"
            "b"
          ]);
      };
      expected = {
        crossArm = false;
        dotted = false;
      };
    };
    test-a-schedule-over-names-carrying-the-separator-orders = {
      expr = order {
        consumer = v.unit {
          relation = rel "a/b" "c";
          target = root "x/b" "c";
          mode = "nest";
        };
        producer = v.unit {
          relation = rel "x" "b/c";
          target = root "a" "b/c";
          mode = "nest";
        };
      };
      expected = [
        "consumer"
        "producer"
      ];
    };
    test-control-one-tuple-keys-equal-and-a-separator-free-schedule-orders = {
      expr = {
        root = v.placement.targetKey (root "a/b" "c") == v.placement.targetKey (root "a/b" "c");
        cell = v.cell "a/b" "c" "input" == v.cell "a/b" "c" "input";
        schedule = order {
          consumer = v.unit {
            relation = rel "a/b" "c";
            target = root "x-b" "c";
            mode = "nest";
          };
          producer = v.unit {
            relation = rel "x" "b/c";
            target = root "a-" "b/c";
            mode = "nest";
          };
        };
      };
      expected = {
        root = true;
        cell = true;
        schedule = [
          "consumer"
          "producer"
        ];
      };
    };
  };
}
