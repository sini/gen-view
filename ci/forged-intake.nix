# A TAG-TESTED INTAKE RE-CHECKS THE ELEMENT IT ADMITS (den-hoag-uw098; p79do Q1: a tag is a CLAIM).
#
# Three families of cell, on `testsError` because their subject is a refusal, or a value whose
# failure mode is a throw the batch asserter behind `checks.default` would crash on rather than
# report (see `tests-error.nix`'s header):
#
#   forged-intake    one cell per tag-tested intake: a genuine element with ONE structural field
#                    forged keeps the genuine tag, and the intake refuses it by name. Before the
#                    re-check each of these aborted uncatchably, answered differently, or admitted.
#   forged-lazy      the re-check forces no CONTENT: a relation whose walk throws is still placed and
#                    scheduled, because neither door reads what the walk produces.
#   genuine-parity   a shape is never stricter than its constructor: every element a constructor
#                    builds, over every declared arm, passes every door it can reach.
{
  genView,
  genPrelude,
  graph,
  ...
}:
let
  v = genView;
  f = import ./fixture.nix { inherit genView; };
  carrierLib = import ../lib/carrier.nix {
    prelude = genPrelude;
    inherit graph;
  };
  refused = expr: msg: {
    expr = builtins.deepSeq expr true;
    expectedError = {
      type = "ThrownError";
      inherit msg;
    };
  };
  root = scope: channel: v.placement.targets.root { inherit scope channel; };
  rootTarget = root "leaf" "settings";
  outTarget = v.placement.targets.output { path = [ "out" ]; };
  gUnit = v.unit {
    inherit (f) relation;
    target = rootTarget;
    mode = "merge";
  };
  carrierArgs = {
    inherit (f) labels relations;
    relatumLabels = f.roles;
    labelWellFormedness = f.admission;
    labelOrder = f.order;
    dataOrder = f.key;
  };
  vd = over: v.viewDefinition (f.definitionArgs // over);

  # gen-graph's declared-edges marker, carried by hand-built values (P3 / Q3).
  ref = graph.mkNodeRef {
    isRegistered =
      n:
      builtins.elem n [
        "a"
        "b"
      ];
  };
  genuineEdges = graph.mkDeclaredEdges [
    {
      from = ref "a";
      to = ref "b";
    }
  ];
  mark = {
    inherit (genuineEdges) _type;
  };
  schedule =
    dd:
    let
      r = v.boundedWellDefinedSchedule {
        nodes = [
          "a"
          "b"
        ];
        declaredDependencies = dd;
        equations = { };
        admitsCycle = _: false;
      };
    in
    {
      inherit (r.condensation) sccs;
      ea = r.edges "a";
    };

  # A walk that throws: the planted CONTENT. A door that forces it fails this family.
  walkThrows = f.mkRelation {
    graph = v.scopeGraph {
      inherit (f) carrier scopes;
      edges = f.edges // {
        parent = _: throw "gen-view forged-lazy: the walk was forced";
      };
      data = f.authored f.datums;
    };
  };

  # ── GENUINE PARITY — every declared arm of every constructor, at every door ──
  relObs = r: {
    inherit (r) value name;
    cs = map (c: c.scope) r.contributions;
  };
  mkDef = o: v.viewDefinition (f.definitionArgs // o);
  mkRel = o: f.mkRelation o;
  doors = r: {
    rel = relObs r;
    reads = v.readsOf r;
    writesRoot = v.writesOf {
      relation = r;
      target = root "leaf" r.name;
      mode = "merge";
    };
    writesOut = v.writesOf {
      relation = r;
      target = v.placement.targets.output {
        path = [
          "o"
          "p"
        ];
      };
      mode = "nest";
    };
    order1 = v.accumulatorOrder {
      units.a = v.unit {
        relation = r;
        target = root "leaf" r.name;
        mode = "merge";
      };
    };
    order2 = v.accumulatorOrder {
      units = {
        a = v.unit {
          relation = r;
          target = root "leaf" r.name;
          mode = "merge";
        };
        b = v.unit {
          relation = r;
          target = v.placement.targets.output { path = [ "q" ]; };
          mode = "nest-verbatim";
        };
      };
    };
    fold = map (pl: pl.placed) (
      v.orderedFoldOf {
        units.a = v.unit {
          relation = r;
          target = root "leaf" r.name;
          mode = "nest";
        };
        path = [ "p" ];
      }
    );
    trace = v.renderTrace (
      v.trace {
        relation = r;
        placement = f.placement // {
          target = root "leaf" r.name;
        };
      }
    );
    mapped = relObs (
      v.transform.map {
        relation = r;
        name = "m";
        f = c: c.datum;
      }
    );
    scanned = relObs (
      v.transform.scan {
        relation = r;
        name = "s";
        f = _: c: c.datum;
        empty = r.definition.empty;
      }
    );
    overed = relObs (
      v.transform.over {
        relation = r;
        name = "o";
        f = cs: builtins.filter (_: true) cs;
      }
    );
  };
  emptyWord = v.labelWellFormedness {
    alphabet = f.labels;
    expression = "";
  };
  scenarios = {
    fixture = f.relation;
    tie-refuse = mkRel { definition = mkDef { tieSet = v.tieSets.refuse; }; };
    tie-orderedFold = mkRel {
      definition = mkDef {
        tieSet = v.tieSets.orderedFold {
          order = [
            "inc"
            "mid"
            "root"
          ];
        };
      };
    };
    comb-attrsShallow = mkRel {
      definition = mkDef {
        combine = v.combines.attrsShallow;
        empty = { };
      };
      graph = v.scopeGraph {
        inherit (f) carrier scopes edges;
        data = [
          {
            scope = "root";
            relation = "import";
            datum.r = 1;
          }
        ];
      };
    };
    comb-setUnion-acc = mkRel {
      definition = mkDef { combine = v.combines.setUnion { acc = true; }; };
    };
    comb-setUnion-noacc = mkRel {
      definition = mkDef { combine = v.combines.setUnion { acc = false; }; };
    };
    dedup-byDatum = mkRel {
      definition = mkDef { dedup = v.dedups.byDatum; };
      graph = f.dupGraph;
    };
    dedup-byKey = mkRel {
      definition = mkDef { dedup = v.dedups.byKey { keyOf = c: c.datum; }; };
      graph = f.dupGraph;
    };
    dir-inbound = mkRel {
      definition = mkDef {
        direction = "inbound";
        root = "root";
      };
    };
    perScopeKey = mkRel { definition = mkDef { channel = f.perScopeKey; }; };
    flatOrder = mkRel { orderMark = f.flatOrder; };
    comp-movement = mkRel { definition = f.mkDefinition { }; };
    comp-topology = mkRel {
      definition = v.compositions.topology (
        builtins.removeAttrs (f.definitionArgs // { channel = "settings"; }) [ "distance" ]
      );
    };
    comp-registry = mkRel {
      definition = v.compositions.registry (
        builtins.removeAttrs (
          f.definitionArgs
          // {
            channel = "settings";
            entityOf = c: c.scope;
          }
        ) [ "distance" ]
      );
    };
    marks-include = mkRel { marks = f.includeMark; };
    roles-empty = mkRel {
      graph = v.scopeGraph {
        carrier = v.carrier (carrierArgs // { relatumLabels = v.relatumLabels { names = [ ]; }; });
        inherit (f) scopes edges;
        data = f.authored f.datums;
      };
    };
    data-empty = mkRel {
      graph = v.scopeGraph {
        inherit (f) carrier scopes edges;
        data = [ ];
      };
    };
    void-graph = mkRel { graph = f.voidGraph; };
    extra-field = f.relation // {
      annotation = "x";
    };
    chain-map = v.transform.map {
      inherit (f) relation;
      name = "settings";
      f = c: c.datum;
    };
    # The lawful EMPTY-WORD expression `""`: the constructor checks `isString`, and so must the shape.
    wf-empty-word = mkRel { definition = mkDef { admission = emptyWord; }; };
  };
  # The doors of one scenario that REFUSE a genuine element. `[ ]` is parity.
  refusedDoors =
    r:
    let
      d = doors r;
    in
    builtins.filter (n: !(builtins.tryEval (builtins.deepSeq d.${n} true)).success) (
      builtins.attrNames d
    );
in
{
  config = {
    flake.testsError.forged-intake = {
      test-labelWellFormedness-alphabet-member =
        refused
          (v.labelWellFormedness {
            alphabet = f.labels // {
              member = 42;
            };
            expression = "(parent|include)*";
          })
          "^gen-view\\.labelWellFormedness: field 'alphabet\\.member' is 42; a edgeLabels element's 'member' is a function\\..*$";
      test-labelOrder-alphabet-letters =
        refused
          (v.labelOrder {
            alphabet = f.labels // {
              letters = 42;
            };
            layers = [
              [ "include" ]
              [ "parent" ]
            ];
            endOfPath = -1;
          })
          "^gen-view\\.labelOrder: field 'alphabet\\.letters' is 42; a edgeLabels element's 'letters' is a list\\..*$";
      test-carrier-labels = refused (v.carrier (
        carrierArgs
        // {
          labels = f.labels // {
            member = 42;
          };
        }
      )) "^gen-view\\.carrier: field 'labels\\.member' is 42; .*$";
      test-carrier-labelWellFormedness =
        refused
          (v.carrier (
            carrierArgs
            // {
              labelWellFormedness = f.admission // {
                alphabet = 42;
              };
            }
          ))
          "^gen-view\\.carrier: field 'labelWellFormedness\\.alphabet' is not a edgeLabels carrier element \\(found a int\\).*$";
      test-carrier-labelOrder = refused (v.carrier (
        carrierArgs
        // {
          labelOrder = f.order // {
            alphabet = 42;
          };
        }
      )) "^gen-view\\.carrier: field 'labelOrder\\.alphabet' is not a edgeLabels carrier element .*$";
      test-carrier-dataOrder =
        refused
          (v.carrier (
            carrierArgs
            // {
              dataOrder = f.key // {
                channel = 42;
              };
            }
          ))
          "^gen-view\\.carrier: field 'dataOrder\\.channel' is 42; a dataOrder element's 'channel' is a non-empty string\\..*$";
      test-carrier-relations = refused (v.carrier (
        carrierArgs
        // {
          relations = f.relations // {
            member = 42;
          };
        }
      )) "^gen-view\\.carrier: field 'relations\\.member' is 42; .*$";
      test-carrier-relatumLabels = refused (v.carrier (
        carrierArgs
        // {
          relatumLabels = f.roles // {
            names = 42;
          };
        }
      )) "^gen-view\\.carrier: field 'relatumLabels\\.names' is 42; .*$";
      test-scopeGraph-carrier = refused (v.scopeGraph {
        carrier = f.carrier // {
          labels = 42;
        };
        inherit (f) scopes edges;
        data = f.authored f.datums;
      }) "^gen-view\\.scopeGraph: field 'carrier\\.labels' is not a edgeLabels carrier element .*$";
      # Before the re-check this answered `[ ]` where the genuine graph answers `[ [ "inc" ] ]`.
      test-relationEntries-graph =
        refused
          (v.relationEntries {
            graph = f.graph // {
              datumsAt = 42;
            };
            scope = "inc";
            relation = "import";
            wellFormed = _: true;
          })
          "^gen-view\\.relationEntries: field 'graph\\.datumsAt' is 42; a scopeGraph element's 'datumsAt' is an attrset\\..*$";
      test-viewDefinition-admission =
        refused
          (vd {
            admission = f.admission // {
              alphabet = 42;
            };
          })
          "^gen-view\\.viewDefinition: field 'admission\\.alphabet' is not a edgeLabels carrier element .*$";
      test-viewDefinition-order = refused (vd {
        order = f.order // {
          alphabet = 42;
        };
      }) "^gen-view\\.viewDefinition: field 'order\\.alphabet' is not a edgeLabels carrier element .*$";
      test-viewDefinition-channel = refused (vd {
        channel = f.key // {
          channel = 42;
        };
      }) "^gen-view\\.viewDefinition: field 'channel\\.channel' is 42; .*$";
      test-viewDefinition-tieSet =
        refused
          (vd {
            tieSet = v.tieSets.union // {
              order = 42;
            };
          })
          "^gen-view\\.viewDefinition: field 'tieSet\\.order' is 42; a tieSet element's 'order' is null\\..*$";
      test-viewDefinition-combine =
        refused
          (vd {
            combine = v.combines.listAppend // {
              setSemilattice = 42;
            };
          })
          "^gen-view\\.viewDefinition: field 'combine\\.setSemilattice' is 42; a combine element's 'setSemilattice' is a bool\\..*$";
      test-viewDefinition-dedup =
        refused
          (vd {
            dedup = v.dedups.none // {
              keyOf = 42;
            };
          })
          "^gen-view\\.viewDefinition: field 'dedup\\.keyOf' is 42; a dedup element's 'keyOf' is null\\..*$";
      # Before: the forged name was carried into the relation's own `name`.
      test-viewRelation-definition =
        refused
          (f.mkRelation {
            definition = f.definition // {
              name = 42;
            };
          }).name
          "^gen-view\\.viewRelation: field 'definition\\.name' is 42; .*$";
      # Before: an empty relation.
      test-viewRelation-graph =
        refused
          (f.mkRelation {
            graph = f.graph // {
              datumsAt = 42;
            };
          }).value
          "^gen-view\\.viewRelation: field 'graph\\.datumsAt' is 42; .*$";
      test-viewRelation-orderMark =
        refused
          (f.mkRelation {
            orderMark = f.identityMark // {
              rankOf = 42;
            };
          }).value
          "^gen-view\\.viewRelation: field 'orderMark\\.rankOf' is 42; a labelOrder element's 'rankOf' is a function\\..*$";
      # `materialized`, reached through `writesOf`: before, admitted.
      test-materialized-at-writesOf = refused (v.writesOf
        {
          relation = f.relation // {
            definition = 42;
          };
          target = rootTarget;
          mode = "merge";
        }
      ) "^gen-view\\.writesOf: field 'relation\\.definition' is not a viewDefinition carrier element .*$";
      # CONTENT, checked by its reader and only there.
      test-readsOf-contributions =
        refused
          (v.readsOf (
            f.relation
            // {
              contributions = 42;
            }
          ))
          "^gen-view\\.readsOf: field 'relation\\.contributions' is 42; a view relation's contributions are a list of records$";
      test-writesOf-target =
        refused
          (v.writesOf {
            inherit (f) relation;
            target = outTarget // {
              arm = 42;
            };
            mode = "merge";
          })
          "^gen-view\\.writesOf: field 'target\\.arm' is 42, which is not one of the declared arms \\(output, root\\)$";
      test-unit-target =
        refused
          (v.unit {
            inherit (f) relation;
            target = rootTarget // {
              arm = 42;
            };
            mode = "merge";
          })
          "^gen-view\\.unit: field 'target\\.arm' is 42, which is not one of the declared arms \\(output, root\\)$";
      # The bead's flagship: a one-unit schedule never reads a unit's relation, so it answered
      # `[ "a" ]` over a unit that carries no relation at all.
      test-accumulatorRelation-units =
        refused
          (v.accumulatorOrder {
            units.a = gUnit // {
              relation = 42;
            };
          })
          "^gen-view\\.accumulatorRelation: field 'units\\.relation' is not a viewRelation carrier element .*$";
      test-trace-contributions = refused (v.trace {
        relation = f.relation // {
          contributions = 42;
        };
        inherit (f) placement;
      }) "^gen-view\\.trace: field 'relation\\.contributions' is 42; .*$";
      test-transform-viewIn = refused (v.transform.over {
        relation = f.relation // {
          definition = 42;
        };
        name = "o";
        f = cs: cs;
      }) "^gen-view\\.over: field 'relation\\.definition' is not a viewDefinition carrier element .*$";

      # ── gen-graph's declared-edges marker at `boundedWellDefinedSchedule` (Q3) ──
      test-control-a-genuine-declared-relation-schedules = {
        expr = schedule genuineEdges;
        expected = {
          sccs = [
            [ "b" ]
            [ "a" ]
          ];
          ea = [ "b" ];
        };
      };
      test-declared-index-not-a-set = refused (schedule (
        mark
        // {
          index = 42;
          dependencies = _: [ ];
        }
      )) "^gen-view\\.boundedWellDefinedSchedule: field 'declaredDependencies\\.index' is 42; .*$";
      test-declared-index-target-not-a-list =
        refused
          (schedule (
            mark
            // {
              index.a = 42;
              dependencies = _: [ ];
            }
          ))
          "^gen-view\\.boundedWellDefinedSchedule: field 'declaredDependencies\\.index' maps 'a' to 42; .*$";
      test-declared-index-missing =
        refused
          (schedule (
            mark
            // {
              dependencies = _: [ ];
            }
          ))
          "^gen-view\\.boundedWellDefinedSchedule: field 'declaredDependencies' carries gen-graph's declared-edges marker with no 'index'; .*$";
      test-declared-dependencies-not-a-function = refused (schedule (
        mark
        // {
          index.a = [ "b" ];
          dependencies = 42;
        }
      )) "^gen-view\\.boundedWellDefinedSchedule: field 'declaredDependencies\\.dependencies' is 42; .*$";
      test-declared-dependencies-missing =
        refused
          (schedule (
            mark
            // {
              index.a = [ "b" ];
            }
          ))
          "^gen-view\\.boundedWellDefinedSchedule: field 'declaredDependencies' carries gen-graph's declared-edges marker with no 'dependencies'; .*$";
      # The edges are DERIVED from the checked `index`, so a forged `dependencies` has nothing to
      # reach: one returning a non-list, and one disagreeing with `index`, both answer the index's
      # relation. Before, the first aborted and the second answered `[ ]` in silence.
      test-declared-dependencies-result-is-never-read = {
        expr = schedule (
          mark
          // {
            index.a = [ "b" ];
            dependencies = _: 42;
          }
        );
        expected = schedule genuineEdges;
      };
      test-declared-dependencies-disagreeing-with-index-is-never-read = {
        expr = schedule (
          mark
          // {
            index.a = [ "b" ];
            dependencies = _: [ ];
          }
        );
        expected = schedule genuineEdges;
      };

      # ── A KIND WITH NO SHAPE IS TAG-TESTED ONLY (gate C1) ──
      # gen-bind's ci imports `carrier.nix` for its own `peerRelation` element; gen-view's own
      # `placement` has no shape either. Both pass, as they did before the re-check.
      test-an-unshaped-kind-of-this-library-passes = {
        expr = (carrierLib.elementOf "probe" "p" "placement" f.placement).__element;
        expected = "placement";
      };
      test-a-foreign-kind-passes = {
        expr =
          (carrierLib.elementOf "probe" "p" "peerRelation" {
            __element = "peerRelation";
            name = "peers";
          }).name;
        expected = "peers";
      };
    };

    # ── LAZINESS: the re-check forces no content ──
    flake.testsError.forged-lazy = {
      test-control-the-walk-is-planted = refused walkThrows.value "^gen-view forged-lazy: the walk was forced$";
      test-writesOf-forces-no-walk = {
        expr = v.writesOf {
          relation = walkThrows;
          target = rootTarget;
          mode = "merge";
        };
        expected = [ "[\"leaf\",\"settings\",\"output\"]" ];
      };
      test-a-one-unit-schedule-forces-no-walk = {
        expr = v.accumulatorOrder {
          units.a = v.unit {
            relation = walkThrows;
            target = rootTarget;
            mode = "merge";
          };
        };
        expected = [ "a" ];
      };
    };

    # ── GENUINE PARITY: no genuine element is refused, over every declared arm (gate C2) ──
    flake.testsError.genuine-parity =
      builtins.mapAttrs
        (_: r: {
          expr = refusedDoors r;
          expected = [ ];
        })
        (
          builtins.listToAttrs (
            map (n: {
              name = "test-${n}";
              value = scenarios.${n};
            }) (builtins.attrNames scenarios)
          )
        )
      // {
        test-the-empty-word-carrier-builds = {
          expr =
            (v.scopeGraph {
              carrier = v.carrier (carrierArgs // { labelWellFormedness = emptyWord; });
              inherit (f) scopes edges;
              data = [ ];
            }).__element;
          expected = "scopeGraph";
        };
        test-an-empty-output-path-is-written = {
          expr = v.writesOf {
            inherit (f) relation;
            target = v.placement.targets.output { path = [ ]; };
            mode = "merge";
          };
          expected = [ "[\"out\",[],\"output\"]" ];
        };
        # The door list is not vacuous: a refusing door is reported by name.
        test-control-a-refusing-door-is-reported = {
          expr = refusedDoors (
            f.relation
            // {
              name = 42;
            }
          );
          # Every door that admits the relation through an intake; `rel` only reads its fields.
          expected = [
            "fold"
            "mapped"
            "order1"
            "order2"
            "overed"
            "reads"
            "scanned"
            "trace"
            "writesOut"
            "writesRoot"
          ];
        };
      };
  };
}
