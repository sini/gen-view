# A datum or key carrying Nix string CONTEXT — a store path, the ordinary delivered case — is
# addressed by its text and DECIDED by `==`, and a dedup collapse keeps every dependency edge: the
# kept datum carries the union of its collapsed twins' contexts (den-hoag-kunjm, the quotient
# rule). Each cell reads the edges off the result; the context-free cells in `relation.nix` are
# the control. The error half is `../tests-error.nix`, `flake.testsError.dedup-context`.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;
  a = builtins.toFile "kunjm-ctx-a" "a";
  b = builtins.toFile "kunjm-ctx-b" "b";
  bareA = builtins.unsafeDiscardStringContext a;
  # equal to `a` in TEXT, carrying `b`'s context: `==` calls them equal
  aWithB = builtins.appendContext bareA (builtins.getContext b);
  pathsOf = s: builtins.attrNames (builtins.getContext s);
  run =
    definition: datums:
    v.viewRelation {
      inherit definition;
      graph = v.scopeGraph {
        inherit (f) carrier scopes edges;
        data = [
          {
            scope = "inc";
            relation = "import";
            datum = builtins.elemAt datums 0;
          }
          {
            scope = "mid";
            relation = "import";
            datum = builtins.elemAt datums 1;
          }
        ];
      };
      marks = f.noMarks;
      orderMark = f.identityMark;
    };
  on =
    definition: datums:
    let
      r = run definition datums;
    in
    {
      kept = builtins.length r.contributions;
      dropped = builtins.length r.dropped;
      # the store paths each kept datum depends on, in walk order
      edges = map (c: pathsOf (builtins.toJSON c.datum)) r.contributions;
    };
  movement =
    dedup:
    f.mkDefinition {
      order = f.flatOrder;
      inherit dedup;
    };
  byDatum = on (movement v.dedups.byDatum);
  byKey = keyOf: on (movement (v.dedups.byKey { inherit keyOf; }));
  registry =
    entityOf:
    on (
      v.compositions.registry {
        channel = "settings";
        relation = "import";
        root = "leaf";
        direction = "outbound";
        inherit (f) admission;
        order = f.flatOrder;
        wellFormed = f.admitAll;
        tieSet = v.tieSets.union;
        empty = [ ];
        combine = v.combines.listAppend;
        dedup = v.dedups.none;
        inherit entityOf;
      }
    );
in
{
  flake.tests.dedup-context = {
    # ── THE ADDRESS: context never reaches an attribute name ──
    test-a-store-path-list-datum-dedups-and-keeps-its-edge = {
      expr = byDatum [
        [ a ]
        [ a ]
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ (pathsOf a) ];
      };
    };
    test-a-store-path-caller-key-dedups = {
      expr = byKey (_: a) [
        [ "p" ]
        [ "q" ]
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ [ ] ];
      };
    };
    test-a-store-path-competition-key-groups = {
      expr = registry (_: a) [
        [ "p" ]
        [ "q" ]
      ];
      expected = {
        kept = 2;
        dropped = 0;
        edges = [
          [ ]
          [ ]
        ];
      };
    };

    # ── THE QUOTIENT: a string datum carries the union of its twins' edges ──
    # ★ The walk-first twin is the context-FREE one, so an address-only repair keeps no edge.
    test-a-string-datum-collapsed-into-its-bare-twin-keeps-the-twins-edge = {
      expr = byDatum [
        bareA
        a
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ (pathsOf a) ];
      };
    };
    test-two-context-differing-equal-strings-collapse-into-the-union = {
      expr = byDatum [
        a
        aWithB
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ (pathsOf (a + b)) ];
      };
    };
    # Under `byKey` the rule reaches a collapse whose DATA are `==`, as under `byDatum`.
    test-a-bykey-collapse-of-equal-data-keeps-the-twins-edge = {
      expr = byKey (_: "K") [
        bareA
        a
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ (pathsOf a) ];
      };
    };
    # ★ PIN: a `byKey` collapse of UNEQUAL data drops the whole datum, as declared; the rule's
    # antecedent is `==`-equal data, so no edge of the dropped datum is carried.
    test-a-bykey-collapse-of-unequal-data-carries-nothing-of-the-dropped-datum = {
      expr = byKey (_: "K") [
        [ bareA ]
        [ b ]
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ [ ] ];
      };
    };
    # Under `byKey` the union reaches a STRING kept datum only: a pointer-shared cyclic datum is
    # addressed by its key and never walked, so its collapse is a value, as it was before the rule.
    test-a-bykey-collapse-of-a-shared-cyclic-datum-is-a-value = {
      expr =
        let
          cyc = {
            self = cyc;
            x = 1;
          };
          r = run (movement (v.dedups.byKey { keyOf = _: "K"; })) [
            cyc
            cyc
          ];
        in
        {
          kept = builtins.length r.contributions;
          dropped = builtins.length r.dropped;
          read = map (c: c.datum.x) r.contributions;
        };
      expected = {
        kept = 1;
        dropped = 1;
        read = [ 1 ];
      };
    };
    # ★ PIN of today's SILENT drop: a `byKey` collapse of `==`-equal NON-string data whose contexts
    # differ keeps the walk-first datum and loses `a`, exactly as before the rule, where `byKey`
    # addressed the key only. A landing that reaches non-string data under `byKey` (den-hoag-kunjm's
    # S1) flips this cell.
    test-a-bykey-nonstring-collapse-of-equal-data-context-dropped-pending-S1 = {
      expr = byKey (_: "K") [
        [ bareA ]
        [ a ]
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ [ ] ];
      };
    };
    # A non-string datum whose twin carries nothing it lacks collapses and keeps its edges.
    test-a-list-datum-collapsed-with-a-bare-twin-keeps-its-own-edge = {
      expr = byDatum [
        [ a ]
        [ bareA ]
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ (pathsOf a) ];
      };
    };
    # den-hoag-eunp3's pin of the held abort (`materialization-refusals`), flipped: a
    # function-bearing datum that carries string context dedups by `==` and keeps its edge.
    test-a-function-bearing-datum-with-string-context-dedups = {
      expr =
        let
          m = { config, ... }: { };
          r = run (movement v.dedups.byDatum) [
            [
              m
              a
            ]
            [
              m
              a
            ]
          ];
        in
        {
          kept = builtins.length r.contributions;
          dropped = builtins.length r.dropped;
          edges = pathsOf (builtins.elemAt (builtins.head r.contributions).datum 1);
        };
      expected = {
        kept = 1;
        dropped = 1;
        edges = pathsOf a;
      };
    };
    # ★ PIN of today's SILENT drop: a context held in a SIBLING of a coercible set is not an edge
    # the walk reads (it stops at the coercion, as the bucket address does), so the collapse keeps
    # the walk-first set and loses `a`. A landing that refuses this shape (den-hoag-kunjm's F1)
    # flips this cell; den-hoag-gkrtw's construct is where the sibling is read.
    test-a-coercible-sets-hidden-sibling-context-dropped-pending-F1 = {
      expr =
        let
          r = run (movement v.dedups.byDatum) [
            [
              {
                outPath = "x";
                extra = bareA;
              }
            ]
            [
              {
                outPath = "x";
                extra = a;
              }
            ]
          ];
        in
        {
          kept = builtins.length r.contributions;
          dropped = builtins.length r.dropped;
          # read the sibling itself: the address and `edgesOf` both stop at `outPath`
          edges = pathsOf (builtins.head (builtins.head r.contributions).datum).extra;
        };
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ ];
      };
    };
    test-control-a-context-free-string-collapse-is-unchanged = {
      expr = byDatum [
        "s"
        "s"
      ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ [ ] ];
      };
    };
  };
}
