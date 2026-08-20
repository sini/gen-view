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
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;

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
  };
}
