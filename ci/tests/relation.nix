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
    relatumLabels = f.roles;
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

  # ── THE DIVERGENT-AT-POSITION-0 FIXTURE, for the visibility order ──
  # `A` is reached by `include`, `D` by `parent·parent`. The two paths diverge at the FIRST
  # position on DISTINCT labels, so whether either shadows the other is decided entirely by
  # whether `<l` orders those two labels — which is the question the layers declaration answers
  # and the rank-word lift used to ignore. There is deliberately no contributor at the
  # intermediate scope, so no prefix relation can mask the outcome.
  divergentGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = [
      "S"
      "A"
      "M"
      "D"
    ];
    edges = {
      include = id: if id == "S" then [ "A" ] else [ ];
      parent =
        id:
        {
          S = [ "M" ];
          M = [ "D" ];
        }
        .${id} or [ ];
    };
    data = f.authored {
      A = [
        {
          relation = "import";
          datum = [ "a" ];
        }
      ];
      D = [
        {
          relation = "import";
          datum = [ "d" ];
        }
      ];
    };
  };
  divergentWith =
    order:
    v.viewRelation {
      definition = f.mkDefinition {
        inherit order;
        root = "S";
      };
      graph = divergentGraph;
      marks = f.noMarks;
    };
  divergentFlat = divergentWith f.flatOrder;
  divergentLayered = divergentWith f.order;

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

  # ══════════════════════════════════════════════════════════════════════════════════════════
  # ── §1.2's DIAMOND, AND ITS FAMILY — AUTHORSHIP-VISIBILITY (den-hoag-2vzn) ──
  #
  # `top` is reached from `leaf` by two paths whose residual derivative states differ:
  #   leaf -parent-> a -include-> top     (state after: the "started on parent" residual)
  #   leaf -include-> b -parent-> top     (state after: the "started on include" residual)
  #
  # ★★★ O0's TWO MASKERS, DEFEATED BOTH. A single-derivative-state admission (e.g. `f.admission`,
  # `(parent|include)*`) collapses both arrivals to ONE class at step 4 before step 6a ever runs —
  # `diamondAdmission` below is ASYMMETRIC so the two states stay distinct. A LAYERED label order
  # (e.g. `f.order`, gen-view's own shipped default) shadows one arrival at step 6 before 6a/6b ever
  # sees two — every declaration below states `f.flatOrder` explicitly, `ci/fixture.nix`'s existing
  # flat binding, never a custom one.
  diamondAdmission = v.labelWellFormedness {
    alphabet = f.labels;
    expression = "parent(include)*|include(parent)*";
  };

  authorshipScopes = [
    "leaf"
    "a"
    "b"
    "top"
  ];

  # `top` reached twice (the diamond); no `rival`. O0, O1, O1b, O2.
  diamondEdges = {
    parent =
      id:
      {
        leaf = [ "a" ];
        b = [ "top" ];
      }
      .${id} or [ ];
    include =
      id:
      {
        leaf = [ "b" ];
        a = [ "top" ];
      }
      .${id} or [ ];
  };
  diamondData = [
    {
      scope = "top";
      relation = "import";
      datum = [ "X" ];
    }
  ];
  diamondGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = authorshipScopes;
    edges = diamondEdges;
    data = diamondData;
  };

  # The SAME graph with `b`'s route removed — `top` reached ONCE. O1's negative control, and O4's
  # single-route subject (multiplied to two declarations below).
  singleRouteEdges = {
    parent = id: { leaf = [ "a" ]; }.${id} or [ ];
    include = id: { a = [ "top" ]; }.${id} or [ ];
  };
  singleRouteGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = authorshipScopes;
    edges = singleRouteEdges;
    data = diamondData;
  };

  # O4 — the same single route, `top`'s datum authored TWICE. Deliberately single-route: the
  # diamond graph would give 2 arrivals × 2 declarations = 4 and make the cell's 2 ambiguous.
  o4Graph = v.scopeGraph {
    carrier = f.carrier;
    scopes = authorshipScopes;
    edges = singleRouteEdges;
    data = diamondData ++ diamondData;
  };

  # ── Z / Y — O2c's discriminator, and O2/O2b's `rival` fixtures ──
  # Z: no diamond, `top` reached ONCE via `a`; `rival` reached once, same route.
  zScopes = [
    "leaf"
    "a"
    "top"
    "rival"
  ];
  zEdges = {
    parent = id: { leaf = [ "a" ]; }.${id} or [ ];
    include =
      id:
      {
        a = [
          "top"
          "rival"
        ];
      }
      .${id} or [ ];
  };
  zData = [
    {
      scope = "top";
      relation = "import";
      datum = [ "X" ];
    }
    {
      scope = "rival";
      relation = "import";
      datum = [ "R" ];
    }
  ];
  zGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = zScopes;
    edges = zEdges;
    data = zData;
  };

  # Y: Z PLUS one more route to `top` alone (`leaf -include-> b -parent-> top`) — `top` now reached
  # twice, `rival` still once. This is the ONE-PAIR-OF-EDGES difference O2c turns on, and it is also
  # O2b's group-of-3 subject (the diamond's two arrivals plus `rival`'s genuinely distinct element).
  yScopes = authorshipScopes ++ [ "rival" ];
  yEdges = {
    parent =
      id:
      {
        leaf = [ "a" ];
        b = [ "top" ];
      }
      .${id} or [ ];
    include =
      id:
      {
        leaf = [ "b" ];
        a = [
          "top"
          "rival"
        ];
      }
      .${id} or [ ];
  };
  yGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = yScopes;
    edges = yEdges;
    data = zData;
  };

  # O3 — two producers, each reached by ONE route, equal content. Not diamond-shaped: O3's question
  # is element identity across DIFFERENT producers, not path multiplicity at one.
  pqScopes = [
    "leaf"
    "p"
    "q"
  ];
  pqEdges = {
    parent =
      id:
      if id == "leaf" then
        [
          "q"
          "p"
        ]
      else
        [ ];
    include = _: [ ];
  };
  pqData = [
    {
      scope = "p";
      relation = "import";
      datum = [ "X" ];
    }
    {
      scope = "q";
      relation = "import";
      datum = [ "X" ];
    }
  ];
  pqGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = pqScopes;
    edges = pqEdges;
    data = pqData;
  };

  # The raw declaration builder shared by every cell below: asymmetric admission, flat order, a
  # CONSTANT key (`_: "settings"`) by default — O0's precondition, satisfied by construction, with
  # every field overridable by name so a cell can differ in exactly one respect.
  mkAsymDef =
    overrides:
    v.viewDefinition (
      {
        channel = v.dataOrder {
          channel = "settings";
          keyOf = _: "settings";
        };
        relation = "import";
        root = "leaf";
        direction = "outbound";
        admission = diamondAdmission;
        order = f.flatOrder;
        wellFormed = f.admitAll;
        distance = s: s.distance + 1;
        tieSet = v.tieSets.union;
        empty = [ ];
        combine = v.combines.listAppend;
        dedup = v.dedups.none;
      }
      // overrides
    );

  runOn =
    graph: definition:
    v.viewRelation {
      inherit definition graph;
      marks = f.noMarks;
    };

  # `true` iff forcing `expr` throws — the same catchable-refusal test §2.8's `registry-split-key-
  # refuses` cell uses, kept local so the throwing-vs-not arms live in `flake.tests` (no `checks
  # .default` crash) rather than needing one `ci/tests-error.nix` cell per tie-set arm for a message
  # that is IDENTICAL across all three (6a refuses before step 7's tieSet dispatch is ever reached).
  throws = expr: !(builtins.tryEval (builtins.deepSeq expr expr)).success;
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

    # ══ FLAT ORDER ⇒ NOTHING SHADOWED, END TO END ══
    #
    # ★★★ THIS IS THE FIXTURE THE DEFECT WAS FOUND ON. `A` is reached by `include` and `D` by
    # `parent·parent` — two paths that DIVERGE AT POSITION 0 on distinct labels. Under a FLAT order
    # those labels share a rank, so Fig. 1 leaves the paths incomparable and NOTHING may shadow.
    # The rank-word lift ordered them anyway and produced an outcome identical to the layered
    # control, so declaring no specificity at all shadowed exactly as much as declaring a real
    # ranking — which made the whole layers design unobservable from the answer.
    #
    # ★ THE LAYERED ARM IS IN THE SAME CELL ON PURPOSE. It is the control: with `include` ranked
    # above `parent` the two labels ARE comparable, shadowing IS licensed, and it happens. A fix
    # that simply stopped ordering things would take this half red.
    test-a-flat-order-shadows-nothing-and-a-layered-one-still-does = {
      expr = {
        flatVisible = map (c: c.scope) divergentFlat.contributions;
        flatShadowed = map (c: c.scope) divergentFlat.shadowed;
        flatValue = divergentFlat.value;
        layeredVisible = map (c: c.scope) divergentLayered.contributions;
        layeredShadowed = map (c: c.scope) divergentLayered.shadowed;
        layeredValue = divergentLayered.value;
      };
      expected = {
        flatVisible = [
          "A"
          "D"
        ];
        flatShadowed = [ ];
        flatValue = [
          "a"
          "d"
        ];
        layeredVisible = [ "A" ];
        layeredShadowed = [ "D" ];
        layeredValue = [ "a" ];
      };
    };

    # ★★ THE DIFFERENTIAL CONTROL ON THE BOUNDED SCAN. The competition computes minimality with a
    # sort by `rankLess` plus a scan against the survivors kept so far — a bound that rests on `<p`
    # refining `rankLess` and on `<p` being transitive. This cell runs the DIRECT pairwise
    # definition ("nothing in the group strictly precedes it") over the same groups and asserts the
    # two agree. If the bound's argument were wrong, the two would disagree here rather than in a
    # consumer's answer six libraries away.
    test-control-the-bounded-minimality-scan-agrees-with-the-pairwise-definition = {
      expr =
        builtins.all
          (
            case:
            let
              members = case.relation.contributions ++ case.relation.shadowed;
              order = case.relation.definition.order;
              pairwise = builtins.filter (
                c: !(builtins.any (o: order.pathPrecedes o.path c.path) members)
              ) members;
            in
            map (c: c.scope) pairwise == map (c: c.scope) case.relation.contributions
          )
          [
            { relation = divergentFlat; }
            { relation = divergentLayered; }
            { relation = f.relation; }
            { relation = f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }; }
          ];
      expected = true;
    };

    # ★ AND THE CONTROL'S OWN CONTROL: the four cases are not all trivially one-element groups, so
    # the agreement above is over groups where minimality has something to decide.
    test-control-the-differential-cases-have-competing-groups = {
      expr = map (r: builtins.length (r.contributions ++ r.shadowed)) [
        divergentFlat
        divergentLayered
        f.relation
      ];
      expected = [
        2
        2
        3
      ];
    };

    # ══ AUTHORSHIP-VISIBILITY (den-hoag-2vzn) — §3's oracles ══

    # ★★★ O0 — THE PRECONDITION EVERY DIAMOND ORACLE BELOW DEPENDS ON. Three declarations, one
    # graph, differing in EXACTLY the field each masker owns. The two masked arms read the SAME
    # `n = 1` regardless of which library evaluates them — a single-derivative-state admission
    # collapses both arrivals at step 4 before 6a/6b ever sees two, and a layered order shadows one
    # at step 6 before 6a/6b ever sees two — so their non-discrimination is exhibited here directly,
    # not asserted. The discriminating arm's RED reading (`n = 2`) is driven separately, against a
    # stashed `lib/`, and recorded in the build report; GREEN is measured here.
    test-o0-two-maskers-each-hide-the-diamond-defect = {
      expr =
        let
          summarize = r: {
            n = builtins.length r.contributions;
            inherit (r) value;
            shadowed = builtins.length r.shadowed;
          };
        in
        {
          discriminating = summarize (runOn diamondGraph (mkAsymDef { }));
          maskedBySymmetricAdmission = summarize (
            runOn diamondGraph (mkAsymDef {
              admission = f.admission;
            })
          );
          maskedByLayeredOrder = summarize (
            runOn diamondGraph (mkAsymDef {
              order = f.order;
            })
          );
        };
      expected = {
        discriminating = {
          n = 1;
          value = [ "X" ];
          shadowed = 0;
        };
        maskedBySymmetricAdmission = {
          n = 1;
          value = [ "X" ];
          shadowed = 0;
        };
        maskedByLayeredOrder = {
          n = 1;
          value = [ "X" ];
          shadowed = 1;
        };
      };
    };

    # ── O1 — A diamond mints exactly ONE element, and the collapsed arrival is recorded NOWHERE ──
    # Asserts the count, the coordinate, the value, `shadowed` AND the survivor's `admission` — the
    # last is the only thing in §3 that pins WHICH arrival 6b keeps (walk-first, never walk-last).
    test-o1-diamond-mints-exactly-one-element = {
      expr =
        let
          r = runOn diamondGraph (mkAsymDef { });
          control = runOn singleRouteGraph (mkAsymDef { });
        in
        {
          n = builtins.length r.contributions;
          element = (builtins.head r.contributions).element;
          value = r.value;
          shadowed = builtins.length r.shadowed;
          survivorAdmission = (builtins.head r.contributions).admission;
          controlN = builtins.length control.contributions;
          controlValue = control.value;
        };
      expected = {
        n = 1;
        element = {
          producer = "top";
          ordinal = 0;
        };
        value = [ "X" ];
        shadowed = 0;
        survivorAdmission = "'parent*";
        controlN = 1;
        controlValue = [ "X" ];
      };
    };

    # ★ THE CONTROL, BENEATH THE PROJECTION: both arrivals really exist and really differ in
    # residual admission state, so O1's `n = 1` is a fold and not a fixture with one route.
    test-control-o1-diamond-has-two-distinguishable-arrivals-before-collapse = {
      expr =
        let
          answers = graph.query {
            mode = "paths";
            graph = diamondGraph.labeled;
            from = "leaf";
            follow = diamondAdmission.expr;
          };
          atTop = builtins.filter (ans: ans.node == "top") answers;
          stateOf =
            ans:
            diamondAdmission.stateKey (
              builtins.foldl' (st: step: diamondAdmission.step step.label st) diamondAdmission.expr ans.path
            );
        in
        {
          witnesses = builtins.length atTop;
          states = builtins.sort builtins.lessThan (map stateOf atTop);
        };
      expected = {
        witnesses = 2;
        states = [
          "'include*"
          "'parent*"
        ];
      };
    };

    # ── O1b — ★★★ A COMPETITION KEY THAT SPLITS AN ELEMENT IS REFUSED BY NAME ──
    # O1's fixture, `keyOf = c: c.admission` — the one element's two arrivals fall into TWO
    # competition groups. Nothing else in this suite reaches step 6a.
    test-o1b-a-split-competition-key-refuses-by-name = {
      expr =
        let
          splitChannel = v.dataOrder {
            channel = "settings";
            keyOf = c: c.admission;
          };
          defWith =
            tieSet:
            mkAsymDef {
              channel = splitChannel;
              inherit tieSet;
            };
        in
        {
          throwsUnderUnion = throws (runOn diamondGraph (defWith v.tieSets.union)).value;
          throwsUnderRefuse = throws (runOn diamondGraph (defWith v.tieSets.refuse)).value;
          throwsUnderOrderedFold =
            throws
              (runOn diamondGraph (defWith (v.tieSets.orderedFold { order = [ "top" ]; }))).value;
        };
      expected = {
        throwsUnderUnion = true;
        throwsUnderRefuse = true;
        throwsUnderOrderedFold = true;
      };
    };

    # ★ LIVE CONTROLS, SAME RUN: a merely path-READING key is not enough to reach 6a. Both give ONE
    # group on this fixture and must NOT refuse — this is O2's GREEN on the same fixture, so without
    # this arm O1b would pass for a step 6a that refuses everything.
    test-control-o1b-path-reading-keys-do-not-split-the-element = {
      expr =
        let
          byScope = v.dataOrder {
            channel = "settings";
            keyOf = c: c.scope;
          };
          byPathShape = v.dataOrder {
            channel = "settings";
            keyOf = c: "d${toString c.distance}-${toString (builtins.length c.path)}";
          };
          rScope = runOn diamondGraph (mkAsymDef {
            channel = byScope;
          });
          rShape = runOn diamondGraph (mkAsymDef {
            channel = byPathShape;
          });
        in
        {
          scopeKeyed = {
            n = builtins.length rScope.contributions;
            value = rScope.value;
          };
          shapeKeyed = {
            n = builtins.length rShape.contributions;
            value = rShape.value;
          };
        };
      expected = {
        scopeKeyed = {
          n = 1;
          value = [ "X" ];
        };
        shapeKeyed = {
          n = 1;
          value = [ "X" ];
        };
      };
    };

    # ★ NEGATIVE CONTROL, SAME RUN: it is the CONSTANT key that keeps O0's own reading out of 6a —
    # its layered-order arm already reads `n = 1, shadowed = 1` with no refusal (O0, above).
    # ★★ MEASURED THIS ROUND, AND STATED BECAUSE IT CONTRADICTS A LITERAL READING OF §3's OWN
    # WORDING: swapping the layered order onto the genuinely SPLIT key (`keyOf = c: c.admission`)
    # does NOT recover that reading. Grouping is a function of `keyOf` alone, fixed at step 6 before
    # `order` is ever consulted for ranking — so a split key gives two SINGLETON groups under
    # EITHER order, and a singleton group has nothing in it to shadow. The refusal fires under both
    # orders; that is 6a's independence from `order`, exhibited rather than assumed, and it is the
    # honest reading of "layered order + split key" on this construction.
    test-control-o1b-the-split-key-refuses-under-either-label-order = {
      expr =
        let
          splitChannel = v.dataOrder {
            channel = "settings";
            keyOf = c: c.admission;
          };
          flatSplit = runOn diamondGraph (mkAsymDef {
            channel = splitChannel;
          });
          layeredSplit = runOn diamondGraph (mkAsymDef {
            channel = splitChannel;
            order = f.order;
          });
          layeredConstant = runOn diamondGraph (mkAsymDef {
            order = f.order;
          });
        in
        {
          flatSplitThrows = throws flatSplit.value;
          layeredSplitThrows = throws layeredSplit.value;
          layeredConstantN = builtins.length layeredConstant.contributions;
          layeredConstantShadowed = builtins.length layeredConstant.shadowed;
        };
      expected = {
        flatSplitThrows = true;
        layeredSplitThrows = true;
        layeredConstantN = 1;
        layeredConstantShadowed = 1;
      };
    };

    # ── O2 — The same diamond does not trip `tieSets.refuse` ──
    # Two positive controls (different producers under refuse; two separate declarations at one
    # producer under refuse), both required to keep throwing at GREEN — without them O2 would pass
    # for a `refuse` arm that stopped firing.
    test-o2-diamond-does-not-trip-tieset-refuse = {
      expr =
        let
          r = runOn diamondGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          differentProducers = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          twoDeclarationsOneProducer = runOn o4Graph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          singleArrival = runOn singleRouteGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
        in
        {
          n = builtins.length r.contributions;
          value = r.value;
          differentProducersThrows = throws differentProducers.value;
          twoDeclarationsOneProducerThrows = throws twoDeclarationsOneProducer.value;
          singleArrivalThrows = throws singleArrival.value;
          singleArrivalN = builtins.length singleArrival.contributions;
          singleArrivalValue = singleArrival.value;
        };
      expected = {
        n = 1;
        value = [ "X" ];
        differentProducersThrows = true;
        twoDeclarationsOneProducerThrows = true;
        singleArrivalThrows = false;
        singleArrivalN = 1;
        singleArrivalValue = [ "X" ];
      };
    };

    # ── O2b — ★★ Every tie-set arm is total on a group the collapse REDUCES ──
    # `Y` is the RED subject (one group of 3: the diamond's two arrivals plus `rival`'s distinct
    # element); `Z` is the GREEN post-collapse twin (the same group reduced to 2). All four arms,
    # both graphs, in one run — four throw and four do not, so neither arm of the instrument is
    # stuck.
    test-o2b-every-tieset-arm-is-total-on-the-reduced-group = {
      expr =
        let
          unionY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.union;
          });
          unionZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.union;
          });
          refuseY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          refuseZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          unrankedY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold { order = [ "rival" ]; };
          });
          unrankedZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold { order = [ "rival" ]; };
          });
          rankedY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold {
              order = [
                "rival"
                "top"
              ];
            };
          });
          rankedZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold {
              order = [
                "rival"
                "top"
              ];
            };
          });
        in
        {
          unionY = {
            n = builtins.length unionY.contributions;
            value = unionY.value;
          };
          unionZ = {
            n = builtins.length unionZ.contributions;
            value = unionZ.value;
          };
          refuseYThrows = throws refuseY.value;
          refuseZThrows = throws refuseZ.value;
          unrankedYThrows = throws unrankedY.value;
          unrankedZThrows = throws unrankedZ.value;
          rankedY = {
            n = builtins.length rankedY.contributions;
            value = rankedY.value;
          };
          rankedZ = {
            n = builtins.length rankedZ.contributions;
            value = rankedZ.value;
          };
        };
      expected = {
        unionY = {
          n = 2;
          value = [
            "X"
            "R"
          ];
        };
        unionZ = {
          n = 2;
          value = [
            "X"
            "R"
          ];
        };
        refuseYThrows = true;
        refuseZThrows = true;
        unrankedYThrows = true;
        unrankedZThrows = true;
        rankedY = {
          n = 2;
          value = [
            "R"
            "X"
          ];
        };
        rankedZ = {
          n = 2;
          value = [
            "R"
            "X"
          ];
        };
      };
    };

    # ── O3 — Two equal-content declarations at DIFFERENT producers stay two ──
    # The RED arm is exhibited by an EXISTING declared policy (`dedups.byDatum`) rather than a
    # mutation, so it is available at both states: the cell fails if the collapse ever reaches
    # content.
    test-o3-equal-content-at-different-producers-stays-two = {
      expr =
        let
          r = runOn pqGraph (mkAsymDef { });
          contentKeyed = runOn pqGraph (mkAsymDef {
            dedup = v.dedups.byDatum;
          });
        in
        {
          n = builtins.length r.contributions;
          producers = map (c: c.element.producer) r.contributions;
          elements = map (c: c.element) r.contributions;
          distinctElements =
            (builtins.elemAt r.contributions 0).element != (builtins.elemAt r.contributions 1).element;
          value = r.value;
          dropped = builtins.length r.dropped;
          contentKeyedN = builtins.length contentKeyed.contributions;
          contentKeyedDropped = builtins.length contentKeyed.dropped;
        };
      expected = {
        n = 2;
        producers = [
          "q"
          "p"
        ];
        elements = [
          {
            producer = "q";
            ordinal = 1;
          }
          {
            producer = "p";
            ordinal = 0;
          }
        ];
        distinctElements = true;
        value = [
          "X"
          "X"
        ];
        dropped = 0;
        contentKeyedN = 1;
        contentKeyedDropped = 1;
      };
    };

    # ── O4 — Two equal-content declarations at ONE producer stay two ──
    # This is the cell `ordinal` exists for: the two elements agree on `producer` and on content,
    # and nothing but the component position separates them.
    test-o4-equal-content-at-one-producer-stays-two = {
      expr =
        let
          r = runOn o4Graph (mkAsymDef { });
          contentKeyed = runOn o4Graph (mkAsymDef {
            dedup = v.dedups.byDatum;
          });
        in
        {
          n = builtins.length r.contributions;
          producers = map (c: c.scope) r.contributions;
          ordinals = map (c: c.element.ordinal) r.contributions;
          value = r.value;
          contentKeyedN = builtins.length contentKeyed.contributions;
          contentKeyedDropped = builtins.length contentKeyed.dropped;
        };
      expected = {
        n = 2;
        producers = [
          "top"
          "top"
        ];
        ordinals = [
          0
          1
        ];
        value = [
          "X"
          "X"
        ];
        contentKeyedN = 1;
        contentKeyedDropped = 1;
      };
    };

    # ── O5 — Every element coordinate comes from the COMPONENT, and nothing else does ──
    # The projection is stated because the two shapes are NOT the same attrset: an entry is
    # `{ scope; relation; datum; ordinal; }`, an element coordinate is `{ producer; ordinal; }`. The
    # cell asserts `nEntries`, the coordinate list AND membership — membership alone passes
    # vacuously against an empty contribution set.
    test-o5-element-coordinates-come-from-the-component = {
      expr =
        let
          coordsOf =
            r:
            map (e: {
              producer = e.scope;
              inherit (e) ordinal;
            }) (builtins.concatMap (s: r.graph.datumsAt.${s} or [ ]) r.graph.scopes);
          check =
            r:
            let
              coords = coordsOf r;
            in
            {
              nEntries = builtins.length coords;
              inherit coords;
              membershipHolds = builtins.all (c: builtins.elem c.element coords) r.contributions;
            };
        in
        {
          diamond = check (runOn diamondGraph (mkAsymDef { }));
          o4 = check (runOn o4Graph (mkAsymDef { }));
        };
      expected = {
        diamond = {
          nEntries = 1;
          coords = [
            {
              producer = "top";
              ordinal = 0;
            }
          ];
          membershipHolds = true;
        };
        o4 = {
          nEntries = 2;
          coords = [
            {
              producer = "top";
              ordinal = 0;
            }
            {
              producer = "top";
              ordinal = 1;
            }
          ];
          membershipHolds = true;
        };
      };
    };
  };
}
