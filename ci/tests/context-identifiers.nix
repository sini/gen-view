# A caller-supplied identifier carrying string context — a scope, a schedule node, a label letter
# or a placement name, e.g. `baseNameOf pkgs.hello` — is KEYED by its text. An attribute name
# cannot carry context, and `==` and the library's own duplicate checks ignore it, so the text is
# the whole of what a key can hold. The caller's value keeps its context. Each cell below reads one
# keying site; its context-free twin is the control. The error half is in `../tests-error.nix`,
# `flake.testsError.context-identifiers`.
{ genView, genPrelude, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;
  ctx = s: "${builtins.substring 0 0 (toString (builtins.toFile "3tsd3-ctx" "x"))}${s}";
  sN = [
    "a"
    "b"
  ];
  mkG =
    {
      sc ? (s: s),
      dc ? (s: s),
    }:
    v.scopeGraph {
      carrier = f.carrier;
      scopes = map sc ([ "r" ] ++ sN);
      edges = {
        parent = _: [ ];
        include = id: if id == "r" then sN else [ ];
      };
      data = map (s: {
        scope = dc s;
        relation = "import";
        datum = [ s ];
      }) sN;
    };
  entries =
    g: scope:
    v.relationEntries {
      graph = g;
      inherit scope;
      relation = "import";
      wellFormed = _: true;
    };
  ranked =
    c:
    v.labelOrder {
      alphabet = f.carrier.labels;
      layers = [
        [ (c "include") ]
        [ "parent" ]
      ];
      endOfPath = -1;
    };
  gathered =
    g:
    map
      (c: [
        c.scope
        c.datum
      ])
      (v.viewRelation {
        definition = f.mkDefinition {
          root = "r";
          order = f.flatOrder;
        };
        graph = g;
        marks = f.noMarks;
        orderMark = f.identityMark;
      }).contributions;
in
{
  flake.tests.context-identifiers = {
    test-entries-at-a-context-carrying-scope-name = {
      expr = map (e: e.datum) (
        entries (mkG {
          sc = ctx;
          dc = ctx;
        }) (ctx "a")
      );
      expected = [ [ "a" ] ];
    };
    test-control-the-context-free-twin-answers-the-same = {
      expr = map (e: e.datum) (entries (mkG { }) "a");
      expected = [ [ "a" ] ];
    };
    test-a-context-carrying-scope-name-keeps-its-context-on-the-entry = {
      expr = builtins.hasContext (builtins.head (entries (mkG { dc = ctx; }) "a")).scope;
      expected = true;
    };
    test-a-view-gathers-a-datum-filed-at-a-context-carrying-scope-name = {
      expr = gathered (mkG {
        dc = ctx;
      });
      expected = gathered (mkG { });
    };
    test-a-context-carrying-letter-is-ranked = {
      expr = (ranked ctx).precedes "include" "parent";
      expected = true;
    };
    test-a-context-carrying-letter-is-looked-up = {
      expr = (ranked (s: s)).precedes (ctx "include") "parent";
      expected = true;
    };
    test-merge-under-a-context-carrying-path = {
      expr =
        (v.placement.place {
          mode = "merge";
          path = [ (ctx "p") ];
          name = "n";
          value = 1;
        }).placed;
      expected = {
        p = 1;
      };
    };
    test-place-under-a-context-carrying-path-and-name = {
      expr =
        (v.placement.place {
          mode = "nest";
          path = [ (ctx "p") ];
          name = ctx "n";
          value = 1;
        }).placed;
      expected = {
        p = {
          n = 1;
        };
      };
    };
    # Every door that reaches a keying site string-checks its input first, so the key's own
    # `isString` guard is read here directly: the discard COERCES an `outPath` set to its text, and
    # a key formed that way would admit the set as a name.
    test-a-non-string-key-is-not-coerced = {
      expr = (import ../../lib/refusal.nix { prelude = genPrelude; }).attrKey { outPath = "include"; };
      expected = {
        outPath = "include";
      };
    };
  };
}
