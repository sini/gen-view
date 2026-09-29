# A datum or key carrying Nix string CONTEXT — a store path, the ordinary delivered case — is
# addressed by its text and DECIDED by `==`, and a dedup collapse keeps its twins' dependency edges
# where it can read them: the kept datum carries the union of its collapsed twins' contexts (den-hoag-kunjm, the quotient
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
    # Under `byKey` a collapse does not force the KEPT datum: the union is computed when the datum
    # is read, so a lazily-throwing kept datum with a twin is a value to a reader of its scope.
    test-a-bykey-collapse-leaves-the-kept-datum-unforced = {
      expr =
        let
          r = run (movement (v.dedups.byKey { keyOf = _: "K"; })) [
            (throw "kept datum forced")
            1
          ];
        in
        {
          dropped = builtins.length r.dropped;
          read = map (c: c.scope) r.contributions;
        };
      expected = {
        dropped = 1;
        read = [ "inc" ];
      };
    };
    # ★ THE STATED BOUNDARY (den-hoag-kunjm S1, a declared ADR-0025 item 1 exception; README
    # "Dedup and string context"): a `byKey` collapse of `==`-equal NON-string data whose contexts
    # differ keeps the walk-first datum and loses `a`. `byKey` addresses the key and never walks the
    # datum, and a walk bounded to refuse deep input would refuse valid input (ADR-0032). This cell
    # flips when den-hoag-gkrtw carries every datum's edges.
    test-a-bykey-nonstring-collapse-of-equal-data-drops-the-twins-edge-the-stated-boundary = {
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
    # W3's refusal reaches NON-derivation coercible sets only: a derivation is read through its
    # `outPath`, as Nix `==` and the bucket address read it, so its siblings are not edges at stake.
    test-a-derivation-with-siblings-collapses-and-keeps-its-edge = {
      expr =
        let
          drv = {
            type = "derivation";
            name = "kunjm-drv";
            outPath = a;
          };
        in
        byDatum [
          [ drv ]
          [ drv ]
        ];
      expected = {
        kept = 1;
        dropped = 1;
        edges = [ (pathsOf a) ];
      };
    };
    # ── THE SET UNION: its `==`-collapse is the same quotient (den-hoag-kunjm F2) ──
    # ★ The walk-first element is the context-FREE one, so prelude `unique` keeps no edge.
    test-the-set-union-collapses-a-string-into-its-bare-twin-and-keeps-the-twins-edge = {
      expr =
        let
          r =
            run
              (f.mkDefinition {
                order = f.flatOrder;
                combine = v.combines.setUnion { acc = true; };
              })
              [
                [ bareA ]
                [ a ]
              ];
        in
        map pathsOf r.value;
      expected = [ (pathsOf a) ];
    };
    # ★ THE STATED BOUNDARY for the union (den-hoag-kunjm F2, pending an owner reading; README
    # "Dedup and string context"): a collapse of `==`-equal NON-string elements keeps the
    # walk-first element and loses `a`. Flips when den-hoag-gkrtw carries every datum's edges.
    test-the-set-union-non-string-collapse-drops-the-twins-edge-the-stated-boundary = {
      expr =
        let
          r = (v.combines.setUnion { acc = true; }).op [ [ bareA ] ] [ [ a ] ];
        in
        {
          length = builtins.length r;
          edges = pathsOf (builtins.head (builtins.head r));
        };
      expected = {
        length = 1;
        edges = [ ];
      };
    };
    # The union walks no non-string content: a pointer-shared cyclic element, and one holding a
    # lazily-throwing attribute, contributed twice, are values (`==` shortcuts on the pointer), as
    # before the rule. An edge walk overflows on the first, uncatchably, and forces the second.
    test-the-set-union-of-a-pointer-shared-cyclic-element-is-a-value = {
      expr =
        let
          cyc = {
            a = 1;
            me = cyc;
          };
          r = (v.combines.setUnion { acc = true; }).op [ cyc ] [ cyc ];
        in
        map (e: e.a) r;
      expected = [ 1 ];
    };
    test-the-set-union-of-a-shared-lazily-throwing-element-is-a-value = {
      expr =
        let
          lazy = {
            a = throw "lazy attribute forced";
          };
          r = (v.combines.setUnion { acc = true; }).op [ lazy ] [ lazy ];
        in
        builtins.all builtins.isAttrs r;
      expected = true;
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
