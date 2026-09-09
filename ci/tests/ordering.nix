# ORACLE O5 — THE ADR-0019 INPUT TYPE HOLDS STRUCTURALLY, plus the accumulator relation it orders.
#
# ★★★ THE INPUT TYPE *IS* THE STRATIFICATION, WHICH IS WHY THIS IS AN ORACLE AND NOT AN ERGONOMIC
# PREFERENCE:
#
#   a consumed query cannot observe a conditional edge
#     ⇒ a query's answer cannot decide whether an edge exists
#       ⇒ the `includes → ¬holds → includes` cycle CANNOT BE WRITTEN
#
# which is Apt, Blair & Walker's Definition 3 clause (2) obtained STRUCTURALLY rather than checked.
#
# ★★ RECORDED BECAUSE THE FAILURE IS SILENT. A relaxation of this input type READS LIKE a
# query-surface change and IS a semantics change: an unstratified program does not throw — it
# quietly has no total model, and every answer it gives is about a model that does not exist. That
# is why the cell below is worth its line even though nothing in the library today would relax it.
{
  genView,
  graph,
  genScope,
  ...
}:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;

  # ══ W1 FIXTURE — boundedWellDefinedSchedule, ORACLE O1/O3/O4/O6/O7 and its own door pair ══
  # A two-node declared relation, `child -> parent`, minted the ONLY way `graph.isDeclaredEdges`
  # admits: through `graph.mkDeclaredEdges`. The SAME two nodes back a `gen-scope` root pair so O7
  # can hand the evaluator the identical declared relation the gate refuses or admits.
  wdsRef = graph.mkNodeRef {
    isRegistered =
      id:
      builtins.elem id [
        "child"
        "parent"
      ];
  };
  wdsContracted = rel: graph.mkDeclaredEdges (builtins.mapAttrs (_: ids: map wdsRef ids) rel);
  wdsDeclaredCyclic = wdsContracted {
    child = [ "parent" ];
    parent = [ "child" ];
  };
  wdsDeclaredAcyclic = wdsContracted { child = [ "parent" ]; };
  wdsNodes = [
    "child"
    "parent"
  ];
  wdsSchedule =
    args:
    v.boundedWellDefinedSchedule (
      {
        nodes = wdsNodes;
        equations = { };
      }
      // args
    );
  wdsKindSynthesized = _: false; # the carve-out is not declared: `admitsCycle` refuses every member
  wdsKindCircular = _: true; # the carve-out IS declared: `admitsCycle` admits every member

  # O7's evaluator witness — `gen-scope`'s OWN roster and fold over the SAME declared relation, so
  # the gate's refusal and the evaluator's success are two answers about one substrate, not two.
  wdsRoots = genScope.buildRoots {
    kinds = genScope.mkKinds [ (genScope.mkKind { name = "host"; }) ];
    parentGraph = genScope.edge "child" "parent";
    decls = {
      parent = {
        v = 10;
      };
      child = {
        v = 1;
      };
    };
    types = {
      parent = "host";
      child = "host";
    };
  };
  wdsUp = id: wdsRoots.nodes.${id}.parent or null;
  # Attributes that read only UPWARD through the parent chain — Sloane's fixpoint plays no part
  # here; this is an ordinary two-attribute grammar, evaluated to show what the gate is not.
  wdsUpward = {
    a = {
      name = "a";
      kind = "synthesized";
      readsAttrs = [ "b" ];
      stratum = "resolution";
      compute = self: id: if wdsUp id == null then (self.node id).decls.v else self.get (wdsUp id) "b";
    };
    b = {
      name = "b";
      kind = "synthesized";
      readsAttrs = [ "a" ];
      stratum = "resolution";
      compute =
        self: id: if wdsUp id == null then (self.node id).decls.v + 1 else self.get (wdsUp id) "a";
    };
  };
  # The control fixture: no cross-attribute reads at all, so its value cannot depend on whether the
  # declared relation the gate inspects is cyclic.
  wdsFlat = {
    a = {
      name = "a";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "resolution";
      compute = self: id: (self.node id).decls.v;
    };
  };
  wdsEvaluatorOn =
    equations: declared:
    (genScope.foldEquations {
      scope = wdsRoots;
      schedule = {
        inherit equations;
      };
      parseParent = wdsUp;
      declaredDependencies = declared;
    }).eval.get
      "child"
      "a";

  # ── TWO UNITS, ONE READING WHERE THE OTHER WRITES ──
  # `producer` gathers under the flat order and NESTS its result into `inc` — so it writes the
  # INPUT cell ⟨inc, settings⟩, the bucket a collector rooted there folds. `consumer` is rooted at
  # `inc` and reads exactly that cell. The schedule must therefore put the producer first.
  producerRelation = f.mkRelation {
    definition = f.mkDefinition {
      order = f.flatOrder;
      root = "mid";
    };
  };
  consumerRelation = f.mkRelation { definition = f.mkDefinition { root = "inc"; }; };

  producer = v.unit {
    relation = producerRelation;
    target = v.placement.targets.root {
      scope = "inc";
      channel = "settings";
    };
    mode = "nest";
  };
  consumer = v.unit {
    relation = consumerRelation;
    target = v.placement.targets.root {
      scope = "leaf";
      channel = "settings";
    };
    mode = "merge";
  };

  # A third unit that writes the SAME CELL as the producer. ★ IT IS NOT A CONFLICT AND MUST NOT BE
  # ORDERED AGAINST IT: output independence is the Bernstein condition this relation deliberately
  # DROPS, and determinism comes from the canonical cell ordering rather than from the schedule.
  coWriter = v.unit {
    relation = f.mkRelation {
      definition = f.mkDefinition {
        order = f.flatOrder;
        root = "root";
      };
    };
    target = v.placement.targets.root {
      scope = "inc";
      channel = "settings";
    };
    mode = "nest";
  };

  units = {
    inherit producer consumer;
  };
in
{
  flake.tests.ordering = {
    # ── THE DOOR REJECTS THE RAW LABELLED-EDGE ACCESSOR BY TYPE ──
    test-the-ordering-door-rejects-the-raw-labelled-edge-accessor = {
      expr = {
        reads = refuses (v.readsOf f.graph.labeled);
        writes = refuses (
          v.writesOf {
            relation = f.graph.labeled;
            target = v.placement.targets.root {
              scope = "leaf";
              channel = "settings";
            };
            mode = "merge";
          }
        );
        makingAUnit = refuses (
          v.unit {
            relation = f.graph.labeled;
            target = v.placement.targets.root {
              scope = "leaf";
              channel = "settings";
            };
            mode = "merge";
          }
        );
      };
      expected = {
        reads = true;
        writes = true;
        makingAUnit = true;
      };
    };

    # ★ THE CONTROL: IT ACCEPTS THE MATERIALIZED PROJECTION. Without it, "rejects the raw accessor"
    # is consistent with a door that rejects everything, and the cell above would be measuring a
    # broken entry point rather than a type.
    test-control-the-door-accepts-the-materialized-projection = {
      expr = {
        reads = v.readsOf f.relation;
        writes = v.writesOf {
          relation = f.relation;
          target = v.placement.targets.root {
            scope = "leaf";
            channel = "settings";
          };
          mode = "merge";
        };
      };
      expected = {
        reads = [ "inc/settings@input" ];
        writes = [ "leaf/settings@output" ];
      };
    };

    # A DEFINITION is not a materialized result either: `readsOf` answers about the membership a
    # walk resolved, and a definition names a root and a policy, never the membership those
    # resolve to.
    test-a-definition-is-not-a-materialized-projection = {
      expr = refuses (v.readsOf f.definition);
      expected = true;
    };

    # ── THE CELL CARRIES A SIDE, AND THE SIDE IS WHAT KEEPS A SELF-GATHERING VIEW ACYCLIC ──
    # A collector reads the INPUT cells of the scopes it gathered and writes an OUTPUT cell at its
    # own root. Without the side those are one cell, and a view that gathers at its own root would
    # read and write it — manufacturing a dependency out of the model rather than the graph.
    test-a-cell-is-a-scope-a-channel-and-a-side = {
      expr = {
        input = v.cell "mid" "settings" "input";
        output = v.cell "mid" "settings" "output";
        differ = v.cell "mid" "settings" "input" != v.cell "mid" "settings" "output";
      };
      expected = {
        input = "mid/settings@input";
        output = "mid/settings@output";
        differ = true;
      };
    };

    # ── THE MODE DECIDES WHETHER A UNIT IS A PRODUCER OR A SINK ──
    # Merging writes an output cell nothing folds; nesting joins the target root's input bucket,
    # which is the nest∘merge decomposition and the only place a real arc comes from.
    test-the-mode-decides-which-side-is-written = {
      expr = map (
        m:
        v.writesOf {
          relation = producerRelation;
          target = v.placement.targets.root {
            scope = "inc";
            channel = "settings";
          };
          mode = m;
        }
      ) v.placement.modes;
      expected = [
        [ "inc/settings@output" ]
        [ "inc/settings@input" ]
        [ "inc/settings@input" ]
      ];
    };

    # THE TERMINAL SINK is a position outside the graph, which no view can read.
    test-the-terminal-sink-is-outside-the-graph = {
      expr = v.writesOf {
        relation = producerRelation;
        target = v.placement.targets.output {
          path = [
            "flake"
            "packages"
          ];
        };
        mode = "merge";
      };
      expected = [ "out:flake.packages@output" ];
    };

    # A target naming a cell this result does not produce is refused: the schedule's arc would
    # otherwise be placed where nothing writes.
    test-a-target-naming-another-channel-refuses = {
      expr = refuses (
        v.writesOf {
          relation = producerRelation;
          target = v.placement.targets.root {
            scope = "inc";
            channel = "elsewhere";
          };
          mode = "nest";
        }
      );
      expected = true;
    };

    # ── THE ACCUMULATOR RELATION: FLOW DEPENDENCE ONLY ──
    test-the-dependency-relation-is-writes-feeding-reads = {
      expr = {
        producerWrites = v.writesOf {
          inherit (producer) relation target mode;
        };
        consumerReads = v.readsOf consumerRelation;
      };
      expected = {
        producerWrites = [ "inc/settings@input" ];
        consumerReads = [ "inc/settings@input" ];
      };
    };

    # ── THE SCHEDULE IS PRODUCERS-FIRST ──
    test-the-schedule-puts-the-producer-before-its-consumer = {
      expr = v.accumulatorOrder { inherit units; };
      expected = [
        "producer"
        "consumer"
      ];
    };

    # ★ THE CONTROL THAT THE SCHEDULE READS THE RELATION AND NOT THE ATTRIBUTE ORDER.
    # `builtins.attrNames` sorts, so "consumer" precedes "producer" alphabetically; a schedule that
    # merely echoed its input would return the other order. This cell is what tells the two apart.
    test-control-the-schedule-is-not-the-alphabetical-order-of-its-input = {
      expr = {
        alphabetical = builtins.attrNames units;
        scheduled = v.accumulatorOrder { inherit units; };
      };
      expected = {
        alphabetical = [
          "consumer"
          "producer"
        ];
        scheduled = [
          "producer"
          "consumer"
        ];
      };
    };

    # ── OUTPUT INDEPENDENCE IS DROPPED, AND THE DROP IS VISIBLE ──
    # Two units writing ONE cell are not ordered against each other: neither depends on the other,
    # and both are still scheduled. A relation that had kept Bernstein's third condition would have
    # to serialize this pair for nothing.
    test-two-units-writing-one-cell-are-not-ordered-against-each-other = {
      expr =
        let
          pair = {
            inherit producer coWriter;
          };
          rel = v.accumulatorRelation { units = pair; };
          depsOf =
            name: map (d: d.name) (rel.edges (builtins.head (builtins.filter (n: n.name == name) rel.nodes)));
        in
        {
          sameCell =
            v.writesOf { inherit (producer) relation target mode; }
            == v.writesOf { inherit (coWriter) relation target mode; };
          producerDeps = depsOf "producer";
          coWriterDeps = depsOf "coWriter";
          scheduled = builtins.length (v.accumulatorOrder { units = pair; });
        };
      expected = {
        sameCell = true;
        producerDeps = [ ];
        coWriterDeps = [ ];
        scheduled = 2;
      };
    };

    # ── THE DOOR THAT COMPOSES THE SCHEDULE WITH PLACEMENT ──
    # Producers-first, each result placed under its own declared mode.
    test-the-ordered-fold-door-places-results-in-schedule-order = {
      expr =
        map
          (p: {
            inherit (p) name mode placed;
          })
          (
            v.orderedFoldOf {
              inherit units;
              path = [ "cfg" ];
            }
          );
      expected = [
        {
          name = "producer";
          mode = "nest";
          placed = {
            cfg.producer = [ "mid" ];
          };
        }
        {
          name = "consumer";
          mode = "merge";
          placed = {
            cfg = [ "inc" ];
          };
        }
      ];
    };

    # ══ O1 — A DECLARED 2-CYCLE THE CARVE-OUT DOES NOT ADMIT REFUSES CATCHABLY ══
    # Unlike the historic `readsAttrs`-based fold (gen-scope `46ab5c8`, whose own mutual-attribute
    # recursion overflows the stack and unwinds THROUGH `tryEval`), this gate's refusal is a
    # `throw`, and `tryEval` catches it clean.
    test-a-declared-cycle-not-admitted-refuses-catchably = {
      expr = refuses (wdsSchedule {
        declaredDependencies = wdsDeclaredCyclic;
        admitsCycle = wdsKindSynthesized;
      });
      expected = true;
    };

    # ── O3, LIVE CONTROL, same run: the same fixture with the cycle broken at one edge is clean ──
    test-control-the-same-relation-with-the-cycle-broken-does-not-refuse = {
      expr =
        (wdsSchedule {
          declaredDependencies = wdsDeclaredAcyclic;
          admitsCycle = wdsKindSynthesized;
        }).condensation.sccs;
      expected = [
        [ "parent" ]
        [ "child" ]
      ];
    };

    # ══ O4 — THE CARVE-OUT: THE SAME 2-CYCLE, ADMITTED PER admitsCycle, BOTH ARMS ONE EVALUATION ══
    test-the-carve-out-admits-a-declared-cycle-every-member-declares = {
      expr = {
        refusedWhenUndeclared = refuses (wdsSchedule {
          declaredDependencies = wdsDeclaredCyclic;
          admitsCycle = wdsKindSynthesized;
        });
        admittedWhenDeclared =
          (wdsSchedule {
            declaredDependencies = wdsDeclaredCyclic;
            admitsCycle = wdsKindCircular;
          }).condensation.sccs;
      };
      expected = {
        refusedWhenUndeclared = true;
        admittedWhenDeclared = [
          [
            "child"
            "parent"
          ]
        ];
      };
    };

    # ══ O6 — THE GATE READS THE CONTRACTED DECLARED RELATION AND NOTHING ELSE (no readsAttrs
    # anywhere): refuses a declared cycle, admits an acyclic one. ★ `directCondensation` IS NOT AN
    # INDEPENDENT CONTROL — `boundedWellDefinedSchedule` never post-filters its success return:
    # `.condensation` IS `graph.condensation { nodes; edges; }` unmodified, so this arm and the
    # subject necessarily compute the identical value from the identical arguments. What it
    # demonstrates is that identity — the returned field is the raw partition, not some filtered
    # derivative of it — not a comparison against an unshared input.
    test-the-gate-reads-the-contracted-declared-relation-and-nothing-else = {
      expr = {
        cyclicRefuses = refuses (wdsSchedule {
          declaredDependencies = wdsDeclaredCyclic;
          admitsCycle = wdsKindSynthesized;
        });
        acyclicSccs =
          (wdsSchedule {
            declaredDependencies = wdsDeclaredAcyclic;
            admitsCycle = wdsKindSynthesized;
          }).condensation.sccs;
        directCondensation =
          (graph.condensation {
            nodes = wdsNodes;
            edges = wdsDeclaredAcyclic.dependencies;
          }).sccs;
      };
      expected = {
        cyclicRefuses = true;
        acyclicSccs = [
          [ "parent" ]
          [ "child" ]
        ];
        directCondensation = [
          [ "parent" ]
          [ "child" ]
        ];
      };
    };

    # ══ O7 — THE DIRECTION IS ONE-WAY: THE GATE REFUSES WHAT THE EVALUATOR COMPUTES ══
    # The collapse (Vogt Definition 3.14, ⟸ only) is sound and not complete: this gate's refusal of
    # a declared cycle is not evidence the evaluator cannot compute a value for it, and this cell
    # exhibits both — the SAME declared relation, one instrument refusing and the other succeeding.
    # Controls, same run: with the declared cycle removed the gate admits and the evaluator still
    # returns a value, and a flat fixture with no cross-attribute reads at all returns a third value
    # that cannot depend on which declared relation the gate was handed.
    test-the-gate-refuses-what-the-evaluator-computes-the-collapse-is-sound-not-complete = {
      expr = {
        gateRefusesCyclic = refuses (wdsSchedule {
          declaredDependencies = wdsDeclaredCyclic;
          admitsCycle = wdsKindSynthesized;
        });
        evaluatorComputesCyclic = wdsEvaluatorOn wdsUpward wdsDeclaredCyclic;
        gateAdmitsAcyclic =
          (wdsSchedule {
            declaredDependencies = wdsDeclaredAcyclic;
            admitsCycle = wdsKindSynthesized;
          }).condensation.sccs;
        evaluatorComputesAcyclic = wdsEvaluatorOn wdsUpward wdsDeclaredAcyclic;
        evaluatorControlFlat = wdsEvaluatorOn wdsFlat wdsDeclaredAcyclic;
      };
      expected = {
        gateRefusesCyclic = true;
        evaluatorComputesCyclic = 11;
        gateAdmitsAcyclic = [
          [ "parent" ]
          [ "child" ]
        ];
        evaluatorComputesAcyclic = 11;
        evaluatorControlFlat = 1;
      };
    };

    # ── W1'S OWN DOOR PAIR: THE SAME PATTERN THE OTHER DOOR ALREADY WRITES ──
    # A hand-assembled attrset carrying an `index` and a `dependencies` is refused BY NAME — the
    # nominal `_type` tag `graph.isDeclaredEdges` checks admits only what `graph.mkDeclaredEdges`
    # minted, not a shape-alike built by hand.
    test-the-schedule-door-rejects-a-hand-assembled-declared-edges-lookalike = {
      expr = refuses (wdsSchedule {
        declaredDependencies = {
          index = {
            child = [ "parent" ];
          };
          dependencies = id: if id == "child" then [ "parent" ] else [ ];
        };
        admitsCycle = wdsKindSynthesized;
      });
      expected = true;
    };

    # ★ THE CONTROL: IT ACCEPTS THE MINTED VALUE. Without it, "rejects the hand-built lookalike" is
    # consistent with a door that rejects everything, and the cell above would be measuring a
    # broken entry point rather than a type.
    test-control-the-schedule-door-accepts-the-minted-declared-edges = {
      expr =
        (wdsSchedule {
          declaredDependencies = wdsDeclaredAcyclic;
          admitsCycle = wdsKindSynthesized;
        }).condensation.sccs;
      expected = [
        [ "parent" ]
        [ "child" ]
      ];
    };
  };
}
