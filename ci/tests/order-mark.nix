# THE ORDER MARK — §3a's gating oracle for M9, one cell per claim the mechanism makes.
#
# THE CLAIM UNDER TEST. The effective visibility order is the LEXICOGRAPHIC PRODUCT of a declared
# order mark with the declaration's own order, MARK OUTER:
#
#     a <ₑ b  ⟺  a <ₘ b  ∨  (a ≃ₘ b ∧ a <q b)
#
# so a query may only refine INSIDE the mark's ties and can never erase or reverse a pair the mark
# declares — which is what lets a mandate BIND without any ecosystem-wide `L̂` being minted.
#
# ★★ THE FIXTURE IS THE DECLINE CASE, and it has to be. `H` holds its own datum, `M` is reached by
# `mandate` and `D` by `default`, and the QUERY ORDER IS HELD FIXED IN EVERY CELL at
# `[["default"] ["mandate"]]` with `$ = -1` — the order a target writes to DECLINE a mandate, `$`
# below every letter so the target's own empty path beats both arrivals. The only variable across
# the cells below is the mark. A fixture whose query was neutral would let a mark "win" against
# nothing and every cell would pass on a library that ignored the query entirely.
#
# ★★★ EVERY CELL HERE ASSERTS ON `contributions` / `value` / `shadowed`, NEVER ON `__element`.
# `viewRelation`'s field check is LAZY BEHIND ITS RESULT: projecting `.__element` from a call
# carrying an undeclared field returns the string `"viewRelation"` at exit 0 with no refusal,
# because `__element` never forces the checked argument set. A cell asserting on it would be green
# on both arms and would have measured nothing. Its siblings do NOT share this — `compositions
# .movement` and `viewDefinition` put `__element` behind their refusal chain — so an author who
# validates the idiom on one of those carries a DEAD CELL here.
{ genView, ... }:
let
  v = genView;

  # ── THE DECLINE FIXTURE ─────────────────────────────────────────────────────────────────────
  letters = [
    "mandate"
    "default"
  ];
  labels = v.edgeLabels { inherit letters; };
  admission = v.labelWellFormedness {
    alphabet = labels;
    expression = "(mandate|default)*";
  };
  relations = v.relations { names = [ "import" ]; };
  roles = v.relatumLabels { names = [ "relatum-target" ]; };
  key = v.dataOrder {
    channel = "settings";
    keyOf = _: "settings";
  };

  order =
    spec:
    v.labelOrder {
      alphabet = labels;
      inherit (spec) layers endOfPath;
    };

  # The target DECLINES: `$` outranks every letter, so `H`'s own empty path beats both arrivals.
  hostileQuery = {
    layers = [
      [ "default" ]
      [ "mandate" ]
    ];
    endOfPath = -1;
  };
  # The MANDATE's mark: `mandate` outranks `$` outranks `default`.
  mandateMark = {
    layers = [
      [ "mandate" ]
      [ ]
      [ "default" ]
    ];
    endOfPath = 1;
  };
  # The IDENTITY: every letter and `$` at one rank, so the product degenerates to the query.
  identityMark = {
    layers = [ letters ];
    endOfPath = 0;
  };
  # BOTH LETTERS TIED and both beating `$` — the mark that leaves the query something to decide.
  tieMark = {
    layers = [ letters ];
    endOfPath = 1;
  };
  # The rejected QUERY-OUTER orientation, flattened by hand and handed to the DEFINITION so the
  # library composes it against an identity mark. `(rank_q, rank_m)` sorted lex is
  # `$ (-1,1)`, `default (0,2)`, `mandate (1,0)` — consecutive ranks 0, 1, 2 with `$` alone at 0.
  queryOuter = {
    layers = [
      [ ]
      [ "default" ]
      [ "mandate" ]
    ];
    endOfPath = 0;
  };

  carrier = v.carrier {
    inherit labels relations;
    relatumLabels = roles;
    labelWellFormedness = admission;
    labelOrder = order hostileQuery;
    dataOrder = key;
  };

  # The DECLINE fixture's wiring: the mandate arrives on `mandate`, the default on `default`.
  declineEdges = {
    mandate = id: if id == "H" then [ "M" ] else [ ];
    default = id: if id == "H" then [ "D" ] else [ ];
  };
  # O2's CONTROL wiring. `M` still holds the mandate's DATUM; only the LETTER it arrives on moves.
  mandateByDefaultEdges = {
    mandate = _: [ ];
    default =
      id:
      if id == "H" then
        [
          "M"
          "D"
        ]
      else
        [ ];
  };

  # The two axes O2 varies — the host's DATUM and the mandate's arrival LETTER — are the only
  # arguments, so an O2 arm differs from every cell above in one named field and nothing else.
  mkGraph =
    { hostDatum, edges }:
    v.scopeGraph {
      inherit carrier edges;
      scopes = [
        "H"
        "M"
        "D"
        # No datum, no out-edge: a query rooted here gathers nothing. It is the CONTROL for the
        # error plane's empty-answer cell — under a well-formed mark this root must MATERIALIZE
        # EMPTY, so that cell's refusal is a verdict on the alphabet and not on the empty gather.
        "Z"
      ];
      data = [
        {
          scope = "H";
          relation = "import";
          datum = hostDatum;
        }
        {
          scope = "M";
          relation = "import";
          datum = [ "from-MANDATE" ];
        }
        {
          scope = "D";
          relation = "import";
          datum = [ "from-DEFAULT" ];
        }
      ];
    };

  graph = mkGraph {
    hostDatum = [ "from-HOST-own" ];
    edges = declineEdges;
  };

  # `run querySpec markSpec` — the WHOLE answer, never a single projection. A cell asserting only
  # "the mandate won" would pass a silent-wrong-answer defect twice over: the unmarked row is the
  # same fixture with the mark made vacuous and the mark-outer row is the same fixture with it made
  # binding, and the two fail for different reasons.
  run = querySpec: markSpec: runFrom "H" querySpec markSpec;

  runFrom =
    root: querySpec: markSpec:
    project (relationOn graph root querySpec markSpec);

  # O2 is the one oracle that varies the GRAPH, so it runs the same projection over a fixture of
  # its own. Everything above reads `run`/`runFrom` and is untouched by that.
  runOn =
    g: querySpec: markSpec:
    project (relationOn g "H" querySpec markSpec);

  relationOn =
    g: root: querySpec: markSpec:
    v.viewRelation {
      definition = v.compositions.movement {
        channel = "settings";
        relation = "import";
        inherit root;
        direction = "outbound";
        inherit admission;
        order = order querySpec;
        wellFormed = _: true;
        tieSet = v.tieSets.union;
        empty = [ ];
        combine = v.combines.listAppend;
        dedup = v.dedups.none;
      };
      graph = g;
      marks = _: [ ];
      orderMark = order markSpec;
    };

  project = r: {
    contributions = map (c: c.scope) r.contributions;
    inherit (r) value;
    shadowed = map (c: {
      inherit (c) scope;
      path = map (s: s.label) c.path;
    }) r.shadowed;
  };

  # O5's SIBLING projection, deliberately not an extension of `project`. The nine cells above are
  # written against `project`'s shape and none of them is about the losing DATUM; widening it would
  # rewrite every one of their `expected` for a field only this oracle reads.
  shadowedDatums =
    querySpec: markSpec:
    map (c: {
      inherit (c) scope datum;
    }) (relationOn graph "H" querySpec markSpec).shadowed;

  # ── O8c's CLOSURE ARMS — rank maps over three letters, and the exhaustive search over them ──
  abc = [
    "a"
    "b"
    "c"
  ];
  # A rank map's RELATION, as the set of ordered pairs it decides.
  relOf =
    rm:
    builtins.concatMap (
      x: builtins.concatMap (y: if rm.${x} < rm.${y} then [ "${x}<${y}" ] else [ ]) abc
    ) abc;
  allRankMaps =
    builtins.concatMap
      (
        i:
        builtins.concatMap
          (
            j:
            map
              (k: {
                a = i;
                b = j;
                c = k;
              })
              [
                0
                1
                2
              ]
          )
          [
            0
            1
            2
          ]
      )
      [
        0
        1
        2
      ];
  sameRel = p: q: builtins.length p == builtins.length q && builtins.all (x: builtins.elem x q) p;
  representations = rel: builtins.length (builtins.filter (rm: sameRel (relOf rm) rel) allRankMaps);

  markRanks = {
    a = 0;
    b = 1;
    c = 1;
  }; # a ≺ b, a ≺ c, b ∥ c
  queryRanks = {
    a = 0;
    b = 0;
    c = 1;
  }; # a ≺ c, b ≺ c, a ∥ b
  intersection = builtins.filter (p: builtins.elem p (relOf queryRanks)) (relOf markRanks);

  # ── O8c's PATH-LEVEL FALSIFIER — three letters, two of them TIED ──
  pLabels = v.edgeLabels {
    letters = [
      "P"
      "I"
      "X"
    ];
  };
  pOrder = v.labelOrder {
    alphabet = pLabels;
    layers = [
      [
        "P"
        "I"
      ]
      [ "X" ]
    ];
    endOfPath = -1;
  };
  asPath =
    ls:
    map (l: {
      label = l;
      target = l;
    }) ls;
in
{
  flake.tests.order-mark = {

    # ══ O8 — A MARK BINDS A HOSTILE QUERY, AND AN IDENTITY MARK CHANGES NOTHING ═══════════════
    # The load-bearing cell. RED and GREEN are the same fixture differing in the mark alone.

    # ★ RED, AND THE CONTROL IN ONE ROW. This is the state a mandate is left in when the target
    # declines: the host's own value wins and both arrivals are shadowed. It is ALSO the control
    # for GREEN — the mark here is the IDENTITY, so a library that hard-wired a winner instead of
    # reading the mark would answer `["M"]` here and this cell would red. The whole answer is
    # asserted, so "reproduces the unmarked result" is byte for byte and not a spot check.
    test-o8-red-the-target-declines-and-the-identity-mark-reproduces-it = {
      expr = run hostileQuery identityMark;
      expected = {
        contributions = [ "H" ];
        value = [ "from-HOST-own" ];
        shadowed = [
          {
            scope = "D";
            path = [ "default" ];
          }
          {
            scope = "M";
            path = [ "mandate" ];
          }
        ];
      };
    };

    # ★★★ GREEN. The mandate BINDS and the hostile query is powerless against it — and no
    # ecosystem-wide alphabet was minted to get there, only a second declaration over the carrier's
    # own `L̂`. `H`'s own datum is now the shadowed one, at the empty path.
    test-o8-green-a-mark-binds-the-hostile-query = {
      expr = run hostileQuery mandateMark;
      expected = {
        contributions = [ "M" ];
        value = [ "from-MANDATE" ];
        shadowed = [
          {
            scope = "H";
            path = [ ];
          }
          {
            scope = "D";
            path = [ "default" ];
          }
        ];
      };
    };

    # ★★ THE REJECTED ORIENTATION, MEASURED RATHER THAN ARGUED. Mark-outer is not a preference:
    # reverse the two components and the mark degenerates to a tie-breaker the query overrules,
    # which reproduces the ADVISORY mandate exactly — the position M9 exists to improve on. Both
    # arms are in ONE cell because a one-armed version would be consistent with a fixture in which
    # the mark never mattered at all.
    test-o8-query-outer-composition-returns-the-red-answer-and-mark-outer-does-not = {
      expr = {
        markOuter = (run hostileQuery mandateMark).contributions;
        queryOuter = (run queryOuter identityMark).contributions;
      };
      expected = {
        markOuter = [ "M" ];
        queryOuter = [ "H" ];
      };
    };

    # ══ O8b — THE QUERY DECIDES INSIDE THE MARK'S TIES AND CANNOT ESCAPE ITS PAIRS ════════════
    # BOTH HALVES OF "NARROWING ONLY" IN ONE ARM. The mark ties the two letters and puts both above
    # `$`; composing the query with it BREAKS that tie (`D` now shadows `M`, antichain 2 → 1) and
    # STILL cannot un-shadow `H` (the pair the mark declared against `$` survives untouched). This
    # is the cell that reds if a future build ever lets a query widen.
    test-o8b-the-query-refines-inside-the-ties-and-cannot-escape-the-marks-pairs = {
      expr = {
        markAlone = run tieMark identityMark;
        markComposedWithQuery = run hostileQuery tieMark;
      };
      expected = {
        markAlone = {
          contributions = [
            "D"
            "M"
          ];
          value = [
            "from-DEFAULT"
            "from-MANDATE"
          ];
          shadowed = [
            {
              scope = "H";
              path = [ ];
            }
          ];
        };
        markComposedWithQuery = {
          contributions = [ "D" ];
          value = [ "from-DEFAULT" ];
          shadowed = [
            {
              scope = "H";
              path = [ ];
            }
            {
              scope = "M";
              path = [ "mandate" ];
            }
          ];
        };
      };
    };

    # ══ O8c — THE CARRIER CLOSURE FACTS, AND ITEM 2's FALSIFIER ═══════════════════════════════

    # ★★ WHY THE LITERAL TRANSFER WAS NOT TAKEN. Relation-intersection is what the boundary mark
    # does to `E`, and on an ORDER it LEAVES gen's carrier: `layers` is a rank map, so `<l` is a
    # strict WEAK order, and weak orders are not closed under ∩. Mark `a≺b, a≺c` intersected with
    # query `a≺c, b≺c` is `{a≺c}`, whose incomparability is not transitive (`a∥b`, `b∥c`, `a≺c`),
    # and NO rank map reproduces it.
    # ★ THE CONTROL IS THE SAME EXHAUSTIVE SEARCH AGAINST A RELATION THAT IS REPRESENTABLE. Without
    # it the zero is equally consistent with a search that can never find anything.
    test-o8c-the-order-intersection-leaves-the-rank-carrier-and-the-search-is-live = {
      expr = {
        intersectionRepresentations = representations intersection;
        controlMarkRepresentations = representations (relOf markRanks);
      };
      expected = {
        intersectionRepresentations = 0;
        controlMarkRepresentations = 3;
      };
    };

    # ★★★ AND WHY THE LEX PRODUCT WAS. The composite key is the PAIR `(rankₘ l, rank_q l)`, and lex
    # on pairs is TOTAL — so the induced relation is a strict weak order and FLATTENS onto the
    # shipped carrier, equal pairs sharing a rank. What step 6 reads is one ordinary `labelOrder`,
    # so `pathPrecedes` and `rankLess` are untouched and the sort-plus-survivors-scan bound
    # survives. THE PAIR IS AN INTERMEDIATE, NEVER A SECOND NUMBER LINE: what M9 admits is ONE more
    # integer lattice over labels, which is exactly what the existing `layers` already admitted.
    # The empty middle layer is `$` holding a composite rank no letter shares, written down.
    test-o8c-the-lexicographic-product-flattens-onto-the-shipped-label-order = {
      expr =
        let
          composed = order mandateMark;
        in
        {
          accepted = composed.__element;
          mandateBeatsEndOfPath = composed.precedes "mandate" "$";
          endOfPathBeatsDefault = composed.precedes "$" "default";
        };
      expected = {
        accepted = "labelOrder";
        mandateBeatsEndOfPath = true;
        endOfPathBeatsDefault = true;
      };
    };

    # ★★ THE FALSIFIER STILL BITES AT THE PATH LEVEL, AND THE COMPOSITION DOES NOT REPAIR IT. The
    # path lift is not integer-representable: `P·X` and `I·P` diverge at position 0 on two letters
    # the order leaves INCOMPARABLE, so `pathPrecedes` is false BOTH ways while the total sort key
    # `rankLess` cheerfully decides the pair. That gap is the antichain the competition keeps, and
    # it is why `rankLess` is a sort bound and never the visibility order.
    # ★ CONTROL: a pair the lift DOES order, so the two falses above are a verdict and not a dead
    # predicate.
    test-o8c-the-path-level-falsifier-fails-as-it-did-and-the-lift-is-live = {
      expr = {
        precedesForward =
          pOrder.pathPrecedes
            (asPath [
              "P"
              "X"
            ])
            (asPath [
              "I"
              "P"
            ]);
        precedesConverse =
          pOrder.pathPrecedes
            (asPath [
              "I"
              "P"
            ])
            (asPath [
              "P"
              "X"
            ]);
        rankLessForward =
          pOrder.rankLess
            (asPath [
              "P"
              "X"
            ])
            (asPath [
              "I"
              "P"
            ]);
        rankLessConverse =
          pOrder.rankLess
            (asPath [
              "I"
              "P"
            ])
            (asPath [
              "P"
              "X"
            ]);
        controlOrderedPair = pOrder.pathPrecedes (asPath [ "P" ]) (asPath [ "X" ]);
      };
      expected = {
        precedesForward = false;
        precedesConverse = false;
        rankLessForward = false;
        rankLessConverse = true;
        controlOrderedPair = true;
      };
    };

    # ══ O8d — THE MARK IS TAKEN AT THE RELATION ═══════════════════════════════════════════════
    # The PLACEMENT cell's constructing half; its refusing half is in `ci/tests-error.nix`, where a
    # message can be asserted.
    #
    # ★★★ WHY THIS CELL EXISTS AT ALL. O8, O8b and O8c each hand ONE order to the definition, so
    # none of them can tell the two `labelOrder` seams apart — and `def.order` is the seam step 6
    # reads. A build that accepted the order mark as a FIELD OF THE VIEW DEFINITION would pass
    # every one of them. That is an input on which the rest of the oracle returns green and the
    # design says red, which is exactly what this cell closes.
    test-o8d-the-mark-is-taken-as-an-argument-of-the-relation-and-reproduces-o8-green = {
      expr = run hostileQuery mandateMark;
      expected = {
        contributions = [ "M" ];
        value = [ "from-MANDATE" ];
        shadowed = [
          {
            scope = "H";
            path = [ ];
          }
          {
            scope = "D";
            path = [ "default" ];
          }
        ];
      };
    };

    # ★ THE CONTROL FOR THE THREE REFUSALS NEXT DOOR. Without it, each of those cells is consistent
    # with a construct that refuses whatever it is handed, and the messages would be about
    # constructors nobody has seen succeed. Both definition constructors and the relation are built
    # here with NO extra field, in the same run, and all three answer.
    test-o8d-control-all-three-constructs-build-when-no-extra-field-is-given = {
      expr =
        let
          defArgs = {
            channel = "settings";
            relation = "import";
            root = "H";
            direction = "outbound";
            inherit admission;
            order = order hostileQuery;
            wellFormed = _: true;
            tieSet = v.tieSets.union;
            empty = [ ];
            combine = v.combines.listAppend;
            dedup = v.dedups.none;
          };
        in
        {
          movement = (v.compositions.movement defArgs).name;
          viewDefinition =
            (v.viewDefinition (
              defArgs
              // {
                channel = key;
                distance = s: s.distance + 1;
              }
            )).name;
          viewRelation = (run hostileQuery identityMark).contributions;
        };
      expected = {
        movement = "settings";
        viewDefinition = "settings";
        viewRelation = [ "H" ];
      };
    };

    # ★ THE CONTROL FOR THE EMPTY-ANSWER REFUSAL NEXT DOOR. A root that gathers nothing under a
    # WELL-FORMED mark must MATERIALIZE EMPTY — it is not an error to find nothing. That is what
    # makes the paired cell in `ci/tests-error.nix` a verdict on the ALPHABET rather than on the
    # empty gather, and it is what would catch a guard that turned every empty answer into a throw.
    test-o8d-control-an-empty-gather-under-a-well-formed-mark-materializes-empty = {
      expr = (runFrom "Z" hostileQuery mandateMark).contributions;
      expected = [ ];
    };

    # ══ O2 — AUTHORITY IS A FUNCTION OF THE LABEL, NOT THE VALUE ══════════════════════════════
    # §3's O2, retained as a cell rather than left in the ephemeral probe it was first measured in.
    # It is the axis the M1 property rests on: what decides a competition is the LETTER a datum
    # arrives on, never the datum's content.
    #
    # ★★ BOTH ARMS SHIP, IN ONE CELL, OVER ONE MARK AND ONE QUERY. The invariant arm alone is
    # consistent with a fixture in which nothing could ever have moved the answer — a dead probe
    # reading green. The control is what makes it a measurement: the same `mandateMark` and the
    # same hostile query, with the mandate's datum re-labelled to arrive on `default`, and the
    # reading FLIPS to the declined answer. The two `expected` values below disagree on every
    # field, so a build that ignored the arrival letter would red the control here.
    test-o2-authority-follows-the-arrival-letter-and-the-relabelled-control-flips = {
      expr = {
        # The host's datum rewritten, and NOTHING else. Content moved; authority did not.
        invariantHostDatumRewritten = runOn (mkGraph {
          hostDatum = [ "from-HOST-REWRITTEN" ];
          edges = declineEdges;
        }) hostileQuery mandateMark;
        # The arrival letter moved, and nothing else. `M` still holds `["from-MANDATE"]`.
        controlMandateArrivesByDefault = runOn (mkGraph {
          hostDatum = [ "from-HOST-own" ];
          edges = mandateByDefaultEdges;
        }) hostileQuery mandateMark;
      };
      expected = {
        # Byte for byte the O8 GREEN answer above — the mandate still binds, and `H`'s new content
        # appears nowhere in the reading.
        invariantHostDatumRewritten = {
          contributions = [ "M" ];
          value = [ "from-MANDATE" ];
          shadowed = [
            {
              scope = "H";
              path = [ ];
            }
            {
              scope = "D";
              path = [ "default" ];
            }
          ];
        };
        # `mandate <l $ <l default`, so a datum arriving on `default` loses to the host's own empty
        # path no matter what it contains. The mark is unchanged; only the letter moved.
        controlMandateArrivesByDefault = {
          contributions = [ "H" ];
          value = [ "from-HOST-own" ];
          shadowed = [
            {
              scope = "M";
              path = [ "default" ];
            }
            {
              scope = "D";
              path = [ "default" ];
            }
          ];
        };
      };
    };

    # ══ O5 — EVERY LOSS STAYS OBSERVABLE, WITH THE LOSING DATUM ═══════════════════════════════
    # §3's O5. `shadowed` carries the losing contribution WHOLE, so the value that lost is readable
    # off the answer and a shadowed declaration is never a silent drop.
    #
    # ★ THE TWO ARMS ARE THE SAME TWO READINGS O8 ASSERTS THE WINNERS OF, so the losing datum is
    # measured against a winner already pinned next door: `from-HOST-own` wins in RED and is the
    # LOSS carried in GREEN, `from-MANDATE` the converse. A build that emitted `shadowed` without
    # the datum, or that carried the WINNER's datum onto the losing record, reds here and nowhere
    # else — no cell above projects this field.
    # ★ Attribution — WHICH mark shadowed it — is a separate surface and is not asserted here.
    test-o5-the-losing-datum-is-readable-off-shadowed-in-both-readings = {
      expr = {
        redTargetDeclines = shadowedDatums hostileQuery identityMark;
        greenMandateBinds = shadowedDatums hostileQuery mandateMark;
      };
      expected = {
        redTargetDeclines = [
          {
            scope = "D";
            datum = [ "from-DEFAULT" ];
          }
          {
            scope = "M";
            datum = [ "from-MANDATE" ];
          }
        ];
        greenMandateBinds = [
          {
            scope = "H";
            datum = [ "from-HOST-own" ];
          }
          {
            scope = "D";
            datum = [ "from-DEFAULT" ];
          }
        ];
      };
    };
  };
}
