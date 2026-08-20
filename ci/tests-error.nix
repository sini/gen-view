# THE SECOND TEST OUTPUT — cells whose subject is an ERROR MESSAGE, and the runner that reads them.
#
# ★★ WHY A SECOND OUTPUT RATHER THAN A SECOND SUITE. `mkCi` builds `checks.default` from an
# asserter that evaluates `t.expr == t.expected` UNCONDITIONALLY and quantifies over
# `config.flake.tests`. A cell with no `expected` and a throwing `expr` therefore CRASHES that
# batch gate rather than failing it. Hosting these on `flake.testsError` puts them outside the
# asserter's quantifier while keeping them live on the nix-unit path.
#
# ★★ AND THE SPLIT IS STRUCTURAL, NOT CONVENTIONAL. This file is NOT under `./tests`, which is the
# whole of `testModules`, so nothing about which cells land in which output depends on a filter
# predicate or an ignore convention a dependency bump could redefine. It reaches the flake through
# `mkCi`'s `extraModules`.
#
# ★★★ THIS OUTPUT IS THE HALF OF ORACLE O1 THAT MAKES A REFUSAL *NAMED*. `ci/tests/refusals.nix`
# asserts that a refusal HAPPENED — a boolean, which `tryEval` can carry. WHICH FIELD it named is a
# claim about the message, and `expectedError` is the only assertion available for that. A suite
# with only the boolean half would go green on a library that refused every omission with one
# undifferentiated message, which is precisely the failure O1 lists: "any refusal is UNNAMED".
#
#   nix-unit --flake ./ci#tests        # the suite
#   nix-unit --flake ./ci#testsError   # these cells
{
  lib,
  genView,
  genInputs,
  ...
}:
let
  f = import ./fixture.nix { inherit genView; };
  v = genView;
in
{
  # Same type as `flake.tests`, because it is the same kind of thing read by the same runner —
  # only the assertion the cells carry differs.
  options.flake.testsError = lib.mkOption {
    type = lib.types.lazyAttrsOf (lib.types.lazyAttrsOf lib.types.raw);
    default = { };
    description = "Test suites whose cells assert an ERROR: { suite.test = { expr; expectedError; }; }. Read by `nix-unit --flake ./ci#testsError`; deliberately outside `flake.tests`, which the batch asserter quantifies over.";
  };

  config = {
    # ── EVERY OMITTED FIELD IS NAMED, ONE CELL PER FIELD ──
    # Generated from the library's own field enumeration, so a thirteenth field cannot arrive
    # without a message cell arriving with it. The pattern is anchored at the front and pins the
    # FIELD NAME, which is the whole content of the claim.
    flake.testsError.named-refusals =
      builtins.listToAttrs (
        map (field: {
          name = "test-omitting-${field}-names-the-field";
          value = {
            expr = builtins.deepSeq (v.viewDefinition (removeAttrs f.definitionArgs [ field ])) true;
            expectedError = {
              type = "ThrownError";
              msg = "^gen-view\\.viewDefinition: required field '${field}' is not declared; every field of this construct is required and total .*$";
            };
          };
        }) v.definitionFields
      )
      // {
        # ★ THE LIVE CONTROL, IN THE SAME INVOCATION. Without it every cell above is consistent
        # with a construct that refuses whatever it is handed, and the messages would be about a
        # constructor nobody has seen succeed. It is an `expected` cell in an `expectedError`
        # output on purpose: a control has to run in the same run as the thing it controls.
        test-control-the-complete-definition-does-not-refuse = {
          expr = (v.viewDefinition f.definitionArgs).name;
          expected = "settings";
        };

        # A FIELD NOBODY DECLARED is named too — the other half of totality, and the arm that makes
        # widening unsayable at the materialization.
        test-an-undeclared-field-is-named = {
          expr = builtins.deepSeq (v.viewRelation {
            definition = f.definition;
            graph = f.graph;
            marks = f.noMarks;
            widen = _: true;
          }) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: field 'widen' is not a field of this construct; the field set is closed .*$";
          };
        };
      };

    # ── THE CARRIER'S OWN REFUSALS NAME THEIR SUBJECT ──
    flake.testsError.carrier-refusals = {
      # The letter, not merely "an unranked letter".
      test-an-unranked-letter-is-named = {
        expr = builtins.deepSeq (v.labelOrder {
          alphabet = f.labels;
          layers = [ [ "parent" ] ];
          endOfPath = -1;
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.labelOrder: letter 'include' is not ranked; the label order is total over the alphabet.*$";
        };
      };

      # The offending name AND the alphabet it is not in, because a caller who wrote a relation
      # name into a path expression needs to see both populations to see the mistake.
      test-a-relation-name-in-a-path-expression-is-named-with-the-alphabet = {
        expr = builtins.deepSeq (v.labelWellFormedness {
          alphabet = f.labels;
          expression = "import*";
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.labelWellFormedness: the expression names 'import', which is not a letter of the alphabet \\(include, parent\\).*$";
        };
      };

      # The undeclared relation and the sort it is not in. ★ THIS IS THE ONE THAT REPLACES A
      # MEASURED SILENT FAILURE: in the grammar this library succeeds, a misspelled channel yields
      # `{ }` and the undeclared-channel check reads `false` even under `deepSeq`.
      test-an-undeclared-relation-is-named-with-the-sort = {
        expr = builtins.deepSeq (v.relationLookup {
          graph = f.graph;
          labeled = f.graph.labeled;
          scope = "inc";
          relation = "not-declared";
          wellFormed = f.admitAll;
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.relationLookup: 'not-declared' is not a name in R \\(broadcast-in, expose-in, import, policy\\).*$";
        };
      };

      # The overlapping name, at the one place that can see both sorts at once.
      test-a-name-in-both-sorts-is-named = {
        expr = builtins.deepSeq (v.carrier {
          labels = f.labels;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
          relations = v.relations {
            names = [
              "import"
              "parent"
            ];
          };
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.carrier: 'parent' is both a letter of L and a name in R; the sorts are disjoint.*$";
        };
      };

      # LIVE CONTROL: the carrier that meets the conditions constructs and carries its five.
      test-control-a-well-formed-carrier-constructs = {
        expr = f.carrier.__element;
        expected = "carrier";
      };
    };

    # ── THE MATERIALIZATION'S REFUSALS NAME THE CHANNEL AND THE CAUSE ──
    flake.testsError.materialization-refusals = {
      # `refuse` names the channel, the count and the contributing scopes — the material a caller
      # needs to resolve the tie, not the verdict that one exists.
      test-a-refused-tie-names-the-channel-and-the-tied-scopes = {
        expr =
          builtins.deepSeq
            (f.mkRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                tieSet = v.tieSets.refuse;
              };
            }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.viewRelation: channel 'settings' declares tieSet 'refuse' and the competition key \"settings\" survives with 2 contributions, from scopes inc, mid.*$";
        };
      };

      # An `orderedFold` whose declared order does not rank a surviving scope names THAT scope: the
      # order is total over the surviving set, and a scope it does not name would otherwise sort to
      # an end nobody declared.
      test-an-unranked-surviving-scope-is-named = {
        expr =
          builtins.deepSeq
            (f.mkRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                tieSet = v.tieSets.orderedFold { order = [ "mid" ]; };
              };
            }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.viewRelation: channel 'settings' declares tieSet 'orderedFold' whose declared order \\(mid\\) does not rank the contributing scope 'inc'.*$";
        };
      };

      # ★ THE LIVE CONTROL FOR BOTH: the SAME fixture under `union` materializes. The two cells
      # above pass by refusing, so without a counterpart they would go green on a fixture that
      # cannot be materialized at all.
      test-control-the-same-fixture-under-union-materializes = {
        expr = (f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }).value;
        expected = [
          "inc"
          "mid"
        ];
      };

      # The ordering door names the raw labelled-edge accessor specifically, so the reader meets
      # the REASON and not just the denial: the input type is the stratification.
      test-the-ordering-door-names-the-raw-accessor = {
        expr = builtins.deepSeq (v.readsOf f.graph.labeled) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.readsOf: field 'relation' is a RAW LABELLED-EDGE ACCESSOR; this door takes the materialized result and only that.*$";
        };
      };

      # LIVE CONTROL: the door accepts the materialized projection.
      test-control-the-ordering-door-accepts-the-materialized-projection = {
        expr = v.readsOf f.relation;
        expected = [ "inc/settings@input" ];
      };
    };

    # THE SECOND HOOK. A second output that nothing runs is a second output that rots, and the
    # wrapper the harness builds bakes `./ci#tests` into its own text, so it cannot be pointed at
    # this one. This is its counterpart, built the same way, under a distinct hook id so the two
    # merge rather than collide.
    perSystem =
      { pkgs, system, ... }:
      {
        pre-commit.settings.hooks.ci-error = {
          enable = true;
          name = "ci-error";
          description = "Run nix-unit error-assertion tests";
          entry = "${
            pkgs.writeShellApplication {
              name = "gen-view-ci-nix-unit-error";
              runtimeInputs = [ genInputs.nix-unit.packages.${system}.default ];
              text = ''
                exec nix-unit --flake ./ci#testsError "$@"
              '';
            }
          }/bin/gen-view-ci-nix-unit-error";
          files = "\\.nix$";
          pass_filenames = false;
        };
      };
  };
}
