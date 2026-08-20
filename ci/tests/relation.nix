# THE MATERIALIZATION, STEP BY STEP — the projection, the competition, the tie-set dispositions,
# the dedup records and the fold.
#
# Each cell here measures ONE step of the construction the oracles quantify over, so a failure
# names the step rather than the whole pipeline.
{ genView, graph, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  scopesOf = r: map (c: c.scope) r.contributions;

  # ── A DIAMOND WITH A SHORTCUT, for the projection ──
  # `a` is reachable from `d` in ONE hop and in TWO, and both arrivals sit in the SAME derivative
  # state — `parent*` steps to `parent*` — so they share a ⟨node, derivative-state⟩ class and the
  # projection has something to fold.
  dLabels = v.edgeLabels { letters = [ "parent" ]; };
  dRelations = v.relations { names = [ "import" ]; };
  dAdmission = v.labelWellFormedness {
    alphabet = dLabels;
    expression = "parent*";
  };
  dOrder = v.labelOrder {
    alphabet = dLabels;
    layers = [ [ "parent" ] ];
    endOfPath = -1;
  };
  dKey = v.dataOrder {
    channel = "d";
    keyOf = c: c.scope;
  };
  dCarrier = v.carrier {
    labels = dLabels;
    labelWellFormedness = dAdmission;
    labelOrder = dOrder;
    dataOrder = dKey;
    relations = dRelations;
  };
  diamond = v.scopeGraph {
    carrier = dCarrier;
    scopes = [
      "a"
      "b"
      "d"
    ];
    edges = {
      parent =
        id:
        {
          d = [
            "b"
            "a"
          ];
          b = [ "a" ];
        }
        .${id} or [ ];
    };
    data = f.authored {
      a = [
        {
          relation = "import";
          datum = [ "a" ];
        }
      ];
    };
  };
  diamondRelation = v.viewRelation {
    definition = v.compositions.topology {
      channel = "d";
      relation = "import";
      root = "d";
      direction = "outbound";
      admission = dAdmission;
      order = dOrder;
      wellFormed = f.admitAll;
      tieSet = v.tieSets.union;
      empty = [ ];
      combine = v.combines.listAppend;
      dedup = v.dedups.none;
    };
    graph = diamond;
    marks = f.noMarks;
  };

  # ── THE PER-SCOPE-KEY RELATION OVER THE DUPLICATE GRAPH, for the dedup records ──
  dupWith =
    dedup:
    v.viewRelation {
      definition = v.viewDefinition (
        f.definitionArgs
        // {
          channel = f.perScopeKey;
          inherit dedup;
        }
      );
      graph = f.dupGraph;
      marks = f.noMarks;
    };
in
{
  flake.tests.relation = {
    # ── THE PROJECTION: A MIN-FOLD OVER `distance` WITHIN EACH ⟨node, derivative-state⟩ CLASS ──
    # Two witnesses reach `a`; one survives, and it is the nearer one. ★ A CARRIER KEYED FINER THAN
    # THE DECLARATION IS NOT A MISMATCH — the projection is part of the materialization and not a
    # chore left to the consumer.
    test-the-projection-keeps-the-nearest-arrival-in-each-class = {
      expr = map (c: {
        inherit (c) scope distance;
        word = map (s: s.label) c.path;
      }) diamondRelation.contributions;
      expected = [
        {
          scope = "a";
          distance = 1;
          word = [ "parent" ];
        }
      ];
    };

    # ★ THE CONTROL: THE FURTHER WITNESS REALLY EXISTS, measured BENEATH the projection on the same
    # walk in the same run. Without it the cell above is equally consistent with a graph on which
    # only one path to `a` was ever available — and the min-fold would then be folding one element
    # and measuring nothing.
    test-control-two-witnesses-reach-the-node-beneath-the-projection = {
      expr =
        let
          answers = graph.query {
            mode = "paths";
            graph = diamond.labeled;
            from = "d";
            follow = dAdmission.expr;
          };
          atA = builtins.filter (ans: ans.node == "a") answers;
        in
        {
          witnesses = builtins.length atA;
          lengths = builtins.sort builtins.lessThan (map (ans: builtins.length ans.path) atA);
          # And both sit in the SAME derivative state, which is what makes them one class rather
          # than two: `parent*` steps to `parent*`, at one hop and at two.
          states = builtins.sort builtins.lessThan (
            map (
              ans:
              dAdmission.stateKey (
                builtins.foldl' (st: step: dAdmission.step step.label st) dAdmission.expr ans.path
              )
            ) atA
          );
        };
      expected = {
        witnesses = 2;
        lengths = [
          1
          2
        ];
        states = [
          "'parent*"
          "'parent*"
        ];
      };
    };

    # ── COMPETITION AND SHADOWING: THE DISCARDED SET IS REPORTED, NEVER DROPPED SILENTLY ──
    test-shadowed-contributions-are-reported-not-dropped = {
      expr = {
        visible = scopesOf f.relation;
        shadowed = map (c: {
          inherit (c) scope distance;
        }) f.relation.shadowed;
      };
      expected = {
        visible = [ "inc" ];
        shadowed = [
          {
            scope = "mid";
            distance = 1;
          }
          {
            scope = "root";
            distance = 2;
          }
        ];
      };
    };

    # ── THE TIE-SET DISPOSITIONS ──
    # `union` — the papers' own arm: the surviving-maximal set IS the answer, in walk order.
    test-union-keeps-the-whole-surviving-maximal-set = {
      expr = (f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }).value;
      expected = [
        "inc"
        "mid"
      ];
    };

    # `orderedFold` — the surviving set is disposed by the DECLARED contribution order, which
    # OVERRIDES the walk order. ★ THAT IS THE POINT: the order must be invariant under presentation
    # order, so a declaration that reverses the walk must actually reverse the result.
    test-orderedfold-disposes-by-the-declared-order-not-the-walk = {
      expr = {
        walkOrder = (f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }).value;
        declaredForward =
          (f.mkRelation {
            definition = f.mkDefinition {
              order = f.flatOrder;
              tieSet = v.tieSets.orderedFold {
                order = [
                  "inc"
                  "mid"
                ];
              };
            };
          }).value;
        declaredReversed =
          (f.mkRelation {
            definition = f.mkDefinition {
              order = f.flatOrder;
              tieSet = v.tieSets.orderedFold {
                order = [
                  "mid"
                  "inc"
                ];
              };
            };
          }).value;
      };
      expected = {
        walkOrder = [
          "inc"
          "mid"
        ];
        declaredForward = [
          "inc"
          "mid"
        ];
        declaredReversed = [
          "mid"
          "inc"
        ];
      };
    };

    # ── DEDUP: EVERY DROP IS A RECORD ──
    # The surface this replaces DECLARED a dedup and enumerated no drops, so an answer that came
    # back short could not be told from a contribution that was never made. Here the drop names the
    # contribution, the survivor it collapsed into, the policy and the key.
    test-every-dedup-drop-is-a-record = {
      expr =
        let
          r = dupWith v.dedups.byDatum;
        in
        {
          kept = map (c: {
            inherit (c) scope datum;
          }) r.contributions;
          dropped = map (d: {
            scope = d.contribution.scope;
            into = d.collapsedInto.scope;
            inherit (d) policy;
          }) r.dropped;
          value = r.value;
        };
      expected = {
        kept = [
          {
            scope = "inc";
            datum = [ "inc" ];
          }
          {
            scope = "mid";
            datum = [ "mid" ];
          }
        ];
        dropped = [
          {
            scope = "root";
            into = "mid";
            policy = "byDatum";
          }
        ];
        value = [
          "inc"
          "mid"
        ];
      };
    };

    # ★ THE CONTROL, SAME FIXTURE, SAME RUN: under `none` NOTHING IS DROPPED and the duplicate
    # survives. Without it "one drop was recorded" is consistent with a gather that only ever found
    # two contributions.
    test-control-under-the-none-policy-the-duplicate-survives-undropped = {
      expr =
        let
          r = dupWith v.dedups.none;
        in
        {
          kept = map (c: c.datum) r.contributions;
          dropped = r.dropped;
        };
      expected = {
        kept = [
          [ "inc" ]
          [ "mid" ]
          [ "mid" ]
        ];
        dropped = [ ];
      };
    };

    # A declared key collapses what structural equality would not — and records that too.
    test-a-declared-dedup-key-collapses-by-the-key = {
      expr =
        let
          r = dupWith (v.dedups.byKey { keyOf = _: "one-bucket"; });
        in
        {
          kept = map (c: c.scope) r.contributions;
          dropped = map (d: d.contribution.scope) r.dropped;
        };
      expected = {
        kept = [ "inc" ];
        dropped = [
          "mid"
          "root"
        ];
      };
    };

    # ── THE FOLD IS ASSOCIATIVE-ONLY: NO REORDER, NO DEDUP BY RANK ──
    # The list's order IS the authority, so the value is the concatenation of the surviving
    # sequence exactly as the tie-set left it. A fold that sorted its answer set — or required a
    # commutative-idempotent monoid to hide that it had — would return the other order here.
    test-the-fold-preserves-the-surviving-sequences-order = {
      expr =
        let
          r = f.mkRelation {
            definition = f.mkDefinition {
              order = f.flatOrder;
              tieSet = v.tieSets.orderedFold {
                order = [
                  "mid"
                  "inc"
                ];
              };
            };
          };
        in
        {
          contributions = map (c: c.scope) r.contributions;
          value = r.value;
        };
      expected = {
        contributions = [
          "mid"
          "inc"
        ];
        value = [
          "mid"
          "inc"
        ];
      };
    };

    # ── THE OTHER COMBINE ARMS FOLD WHAT THEY DECLARE ──
    test-the-set-semilattice-arm-is-idempotent-over-the-surviving-sequence = {
      expr =
        (f.mkRelation {
          definition = v.viewDefinition (
            f.definitionArgs
            // {
              channel = f.perScopeKey;
              combine = v.combines.setUnion { acc = true; };
            }
          );
          graph = f.dupGraph;
        }).value;
      expected = [
        "inc"
        "mid"
      ];
    };

    # ── DIRECTION: THE INBOUND ARM WALKS THE LABELLED TRANSPOSE ──
    # Transpose REVERSES direction rather than erasing it: the label is carried BY the edge, so
    # flipping the edge relation moves the label with it, and the same admission expression still
    # applies. From `root`, the inbound walk reaches `mid` and then `leaf`.
    test-the-inbound-arm-walks-the-labelled-transpose = {
      expr =
        let
          r = f.mkRelation {
            definition = v.viewDefinition (
              f.definitionArgs
              // {
                channel = f.perScopeKey;
                root = "root";
                direction = "inbound";
              }
            );
          };
        in
        map (c: {
          inherit (c) scope distance;
        }) r.contributions;
      expected = [
        {
          scope = "root";
          distance = 0;
        }
        {
          scope = "mid";
          distance = 1;
        }
      ];
    };

    # ★ THE CONTROL: THE OUTBOUND ARM OVER THE SAME ROOT REACHES SOMETHING ELSE. Without it, an
    # inbound answer is consistent with a direction field nothing reads.
    test-control-the-outbound-arm-over-the-same-root-differs = {
      expr =
        let
          r = f.mkRelation {
            definition = v.viewDefinition (
              f.definitionArgs
              // {
                channel = f.perScopeKey;
                root = "root";
                direction = "outbound";
              }
            );
          };
        in
        map (c: c.scope) r.contributions;
      expected = [ "root" ];
    };

    # ── THE RESULT IS NAMED, AND THE NAME IS THE COMPETITION KEY'S OWN ──
    # What competes is exactly what is named, which is why the two are one field at the composition
    # surface.
    test-the-result-carries-its-name = {
      expr = {
        relation = f.relation.name;
        definition = f.relation.definition.name;
      };
      expected = {
        relation = "settings";
        definition = "settings";
      };
    };
  };
}
