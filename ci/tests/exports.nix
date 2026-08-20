# ORACLE O3 — THE SIXTEEN NEEDS-DECLARATION-SURFACE EXPORTS BECOME EXPRESSIBLE, AND THE EXPRESSION
# IS ASSERTED — NOT MERELY EVALUATED.
#
# One case per export. Each carries three things:
#   · a CAPABILITY — a predicate stating what the export map says that export does, asserted
#     against the RESULT and never against "it evaluated";
#   · a FIXTURE built over this library's published surface, which the capability must ACCEPT;
#   · a MUTANT — the same construction with the capability altered in ONE stated respect, which the
#     SAME capability must REJECT.
#
# ★★★ THE MUTANT ARM IS THE CONTROL, AND IT CAN FAIL. A round of this oracle that checked only that
# each fixture evaluated would be measuring the evaluator. A round whose control could not fail —
# a roster's own provenance, say — measures nothing at all. Every mutant below is a value the
# capability must return `false` on, in the same run, through the same predicate.
#
# ★★ WHAT THIS ORACLE DOES *NOT* CLAIM, stated here so it is not read as claiming it: THIS IS A
# VOCABULARY CLAIM, NOT A SEMANTIC-EQUIVALENCE CLAIM. A round trip — a real channel reproducing its
# value through this surface, or a real content fold reproducing through it — is a gap the export
# map itself discloses, and nothing here discharges it.
#
# ★ AND THE ORACLE CLUSTER RETIRES LAST. `trace`, `renderTrace`, `renderEntry`, `traceEntryOf` and
# `edgeSortKey` are the instrument that validates the spec that retires them, so they must be
# expressible HERE before they retire THERE — any plan retiring them alongside the rest removes its
# own oracle.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;
  constructs = thunk: (builtins.tryEval (builtins.deepSeq thunk true)).success;

  # ── A GRAPH THAT EXERCISES ALL THREE OF `traceOf`'s OBLIGATIONS AT ONCE ──
  # `a` and `b` tie under the flat order and carry the SAME datum (a dedup drop); `deep` is
  # shadowed; the containment edge out of `leaf` is withheld by a named mark.
  tLabels = v.edgeLabels {
    letters = [
      "parent"
      "include"
    ];
  };
  tRelations = v.relations { names = [ "import" ]; };
  tAdmission = v.labelWellFormedness {
    alphabet = tLabels;
    expression = "(parent|include)*";
  };
  tFlat = v.labelOrder {
    alphabet = tLabels;
    layers = [
      [
        "parent"
        "include"
      ]
    ];
    endOfPath = -1;
  };
  tKey = v.dataOrder {
    channel = "settings";
    keyOf = _: "settings";
  };
  tCarrier = v.carrier {
    relatumLabels = f.roles;
    labels = tLabels;
    labelWellFormedness = tAdmission;
    labelOrder = tFlat;
    dataOrder = tKey;
    relations = tRelations;
  };
  tGraph = v.scopeGraph {
    carrier = tCarrier;
    scopes = [
      "leaf"
      "a"
      "b"
      "deep"
      "inc"
    ];
    edges = {
      parent =
        id:
        {
          leaf = [
            "a"
            "b"
          ];
          a = [ "deep" ];
        }
        .${id} or [ ];
      include = id: if id == "leaf" then [ "inc" ] else [ ];
    };
    data = f.authored {
      a = [
        {
          relation = "import";
          datum = [ "x" ];
        }
      ];
      b = [
        {
          relation = "import";
          datum = [ "x" ];
        }
      ];
      deep = [
        {
          relation = "import";
          datum = [ "y" ];
        }
      ];
      inc = [
        {
          relation = "import";
          datum = [ "z" ];
        }
      ];
    };
  };
  tMark =
    id:
    if id == "leaf" then
      [
        {
          name = "no-containment";
          admits = l: l != "include";
        }
      ]
    else
      [ ];
  tDefinition =
    dedup:
    v.compositions.movement {
      channel = "settings";
      relation = "import";
      root = "leaf";
      direction = "outbound";
      admission = tAdmission;
      order = tFlat;
      wellFormed = f.admitAll;
      tieSet = v.tieSets.union;
      empty = [ ];
      combine = v.combines.listAppend;
      inherit dedup;
    };
  tRelation =
    dedup:
    v.viewRelation {
      definition = tDefinition dedup;
      graph = tGraph;
      marks = tMark;
    };
  # The SAME graph with no isolation bound. The trace cases use this one because its WALK order
  # (`inc` first, the containment edge being walked before the ancestor edges) differs from its
  # SORT-KEY order (`a`, `b`, `inc`) — and a mutant that leaves the entries in walk order can only
  # be rejected on a fixture where the two orders actually differ.
  tUnbounded = v.viewRelation {
    definition = tDefinition v.dedups.none;
    graph = tGraph;
    marks = f.noMarks;
  };

  # Shared placements, so a mutant differs from its fixture in exactly one respect.
  mergeAtRoot = v.placement.place {
    mode = "merge";
    path = [ "cfg" ];
    name = "settings";
    value = f.relation.value;
  };
  nestAtRoot = mergeAtRoot // {
    mode = "nest";
  };
  entryOf =
    placement:
    v.traceEntryOf {
      contribution = builtins.head f.relation.contributions;
      inherit placement;
    };

  # ── THE SIXTEEN CASES ────────────────────────────────────────────────────────────────────────
  cases = {
    # ── gen-pipe ──

    # A CHANNEL IS A NAMED MATERIALIZED QUERY RESULT, and the field that names it is simultaneously
    # the competition key. The capability therefore has three parts, and the third is the one the
    # shipped surface could not state: competition is NOT VACUOUS.
    channel = {
      capability = r: r.name == "settings" && r.value == [ "inc" ] && r.shadowed != [ ];
      fixture = f.mkRelation {
        definition = v.compositions.channel {
          channel = "settings";
          relation = "import";
          root = "leaf";
          direction = "outbound";
          admission = f.admission;
          order = f.order;
          wellFormed = f.admitAll;
          tieSet = v.tieSets.union;
          empty = [ ];
          combine = v.combines.listAppend;
          dedup = v.dedups.none;
        };
      };
      # ONE RESPECT ALTERED: the competition key is per-scope, which is the shipped default this
      # carrier refuses to have. The gather still answers; nothing competes.
      mutant = f.mkRelation {
        definition = v.viewDefinition (f.definitionArgs // { channel = f.perScopeKey; });
      };
    };

    # COMPOSE'S REMAINDER after acyclicity retires by construction: required-field refusals and
    # discipline validity, at construction.
    compose = {
      capability =
        ctor:
        refuses (ctor (removeAttrs f.definitionArgs [ "dedup" ])) && constructs (ctor f.definitionArgs);
      fixture = v.viewDefinition;
      # ONE RESPECT ALTERED: a constructor that DEFAULTS the omitted field instead of refusing it —
      # which is the whole of what "required-field refusals" means.
      mutant = args: v.viewDefinition ({ dedup = v.dedups.none; } // args);
    };

    # RUN'S REMAINDER: the ASSEMBLY — a declaration becomes a NAMED MATERIALIZED RESULT.
    run = {
      capability =
        assemble:
        let
          r = assemble f.definition;
        in
        r.name == "settings" && r.contributions != [ ] && r.value == [ "inc" ];
      fixture = d: f.mkRelation { definition = d; };
      # ONE RESPECT ALTERED: it returns the gathered contributions WITHOUT folding them, so the
      # named result is not the value the declaration declares.
      mutant =
        d:
        let
          r = f.mkRelation { definition = d; };
        in
        r // { value = map (c: c.datum) r.contributions; };
    };

    # TRACE-OF'S THREE OBLIGATIONS: the shadowing half, the boundary half, and the DEDUP-DROP half
    # — the one with no shipped successor anywhere.
    traceOf = {
      capability = r: r.shadowed != [ ] && r.withheld != [ ] && r.dropped != [ ];
      fixture = tRelation v.dedups.byDatum;
      # ONE RESPECT ALTERED: the dedup policy drops nothing, so the third obligation goes unmet
      # while the other two still read fine — which is exactly the partial successor the map warns
      # about.
      mutant = tRelation v.dedups.none;
    };

    # ── gen-edge ──

    # THE EDGE RECORD'S FOUR SURVIVING COMPONENTS: source and target re-express as the declaration's
    # root / direction / admission / channel; path and mode are placement.
    edge = {
      capability =
        e:
        e.source == "inc/import"
        && e.target == "root:inc/settings"
        && e.path == [ "cfg" ]
        && e.mode == "merge";
      fixture =
        let
          entry = entryOf mergeAtRoot;
        in
        {
          source = v.placement.sourceKey entry.source;
          target = v.placement.targetKey entry.target;
          inherit (entry) path mode;
        };
      # ONE RESPECT ALTERED: the placement mode, which is the M component of the record.
      mutant =
        let
          entry = entryOf nestAtRoot;
        in
        {
          source = v.placement.sourceKey entry.source;
          target = v.placement.targetKey entry.target;
          inherit (entry) path mode;
        };
    };

    # SOURCES' COLLECTED ARM: the receiver-rooted collector, whose members are RESOLVED and
    # ISOLATION-BOUNDED.
    sources = {
      capability = reads: reads == [ "mid/settings@input" ];
      fixture = v.readsOf (f.mkRelation { marks = f.includeMark; });
      # ONE RESPECT ALTERED: the isolation bound is dropped, so the members resolve to a different
      # set — the same collector without the half that makes it bounded.
      mutant = v.readsOf f.relation;
    };

    # TARGETS: the root arm is the declaration's root; the output arm is the TERMINAL SINK, a
    # position outside the graph.
    targets = {
      capability =
        t:
        t.root == "root:leaf/settings"
        && t.output == "out:flake.packages"
        &&
          t.arms == [
            "root"
            "output"
          ];
      fixture =
        let
          root = v.placement.targets.root {
            scope = "leaf";
            channel = "settings";
          };
          output = v.placement.targets.output {
            path = [
              "flake"
              "packages"
            ];
          };
        in
        {
          root = v.placement.targetKey root;
          output = v.placement.targetKey output;
          arms = [
            root.arm
            output.arm
          ];
        };
      # ONE RESPECT ALTERED: the terminal sink is expressed as a ROOT target, which is the collapse
      # the two arms exist to prevent — a sink inside the graph is not a sink.
      mutant =
        let
          root = v.placement.targets.root {
            scope = "leaf";
            channel = "settings";
          };
          asRoot = v.placement.targets.root {
            scope = "flake";
            channel = "packages";
          };
        in
        {
          root = v.placement.targetKey root;
          output = v.placement.targetKey asRoot;
          arms = [
            root.arm
            asRoot.arm
          ];
        };
    };

    # DEFAULT-FOLD, corollary-1 sugar: `collected(subtree R, C) → root(R, C)` with an EMPTY path and
    # the MERGE mode.
    defaultFold = {
      capability = d: d.root == "leaf" && d.channel == "settings" && d.path == [ ] && d.mode == "merge";
      fixture = {
        root = f.definition.root;
        channel = f.definition.name;
        inherit
          (v.placement.place {
            mode = "merge";
            path = [ ];
            name = "settings";
            value = f.relation.value;
          })
          path
          mode
          ;
      };
      # ONE RESPECT ALTERED: a non-empty path, which is no longer the corollary's own sugar.
      mutant = {
        root = f.definition.root;
        channel = f.definition.name;
        inherit
          (v.placement.place {
            mode = "merge";
            path = [ "cfg" ];
            name = "settings";
            value = f.relation.value;
          })
          path
          mode
          ;
      };
    };

    # EDGES-FOR: PER-ROOT derivation.
    edgesFor = {
      capability = scopes: scopes == [ "inc" ];
      fixture =
        map (c: c.scope)
          (f.mkRelation { definition = f.mkDefinition { root = "leaf"; }; }).contributions;
      # ONE RESPECT ALTERED: derived for a DIFFERENT root, which is what makes it per-root at all.
      mutant =
        map (c: c.scope)
          (f.mkRelation { definition = f.mkDefinition { root = "mid"; }; }).contributions;
    };

    # THE CONTENT FOLD: seeded buckets, ORDERED LEFT FOLD, per-mode dispatch, declared-cell write.
    # ★ The capability pins the ORDER, because "ordered left fold" is the half a
    # commutative-idempotent successor would silently drop.
    materialize = {
      capability =
        m:
        m.value == [
          "mid"
          "inc"
        ]
        &&
          m.placed == {
            cfg = [
              "mid"
              "inc"
            ];
          };
      fixture =
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
          inherit (r) value;
          inherit
            (v.placement.place {
              mode = "merge";
              path = [ "cfg" ];
              name = "settings";
              value = r.value;
            })
            placed
            ;
        };
      # ONE RESPECT ALTERED: the fold SORTS its input first — the reorder the associative-only law
      # forbids, and the one that a fold over a sorted answer set performs by construction.
      mutant =
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
          sorted = builtins.sort builtins.lessThan (builtins.concatLists (map (c: c.datum) r.contributions));
        in
        {
          value = sorted;
          placed = {
            cfg = sorted;
          };
        };
    };

    # PROJECT: the membership half, with the DEDUP and ISOLATION dials both live.
    project = {
      capability =
        p:
        p.plain == [
          "inc"
          "a"
          "b"
        ]
        &&
          p.deduped == [
            "inc"
            "a"
          ]
        &&
          p.isolated == [
            "a"
            "b"
          ];
      fixture = {
        plain =
          map (c: c.scope)
            (v.viewRelation {
              definition = tDefinition v.dedups.none;
              graph = tGraph;
              marks = f.noMarks;
            }).contributions;
        deduped =
          map (c: c.scope)
            (v.viewRelation {
              definition = tDefinition v.dedups.byDatum;
              graph = tGraph;
              marks = f.noMarks;
            }).contributions;
        isolated = map (c: c.scope) (tRelation v.dedups.none).contributions;
      };
      # ONE RESPECT ALTERED: the dedup dial is inert — every arm answers the undeduplicated set.
      mutant = {
        plain =
          map (c: c.scope)
            (v.viewRelation {
              definition = tDefinition v.dedups.none;
              graph = tGraph;
              marks = f.noMarks;
            }).contributions;
        deduped =
          map (c: c.scope)
            (v.viewRelation {
              definition = tDefinition v.dedups.none;
              graph = tGraph;
              marks = f.noMarks;
            }).contributions;
        isolated = map (c: c.scope) (tRelation v.dedups.none).contributions;
      };
    };

    # ── THE ORACLE CLUSTER ──

    # TRACE: a TOTAL order over identity-only entries.
    trace = {
      capability =
        t:
        t == builtins.sort (x: y: v.edgeSortKey x < v.edgeSortKey y) t
        && builtins.all (e: !(e ? datum)) t
        && builtins.length t == 3;
      fixture = v.trace {
        relation = tUnbounded;
        placement = mergeAtRoot;
      };
      # ONE RESPECT ALTERED: the entries are left in WALK order instead of sort-key order, on a
      # fixture where the two differ.
      mutant = map (
        c:
        v.traceEntryOf {
          contribution = c;
          placement = mergeAtRoot;
        }
      ) tUnbounded.contributions;
    };

    # RENDER-TRACE: the per-entry rendering, mapped over the whole trace and losing nothing.
    renderTrace = {
      capability =
        rendered:
        let
          t = v.trace {
            relation = tUnbounded;
            placement = mergeAtRoot;
          };
        in
        rendered == map v.renderEntry t;
      fixture = v.renderTrace (
        v.trace {
          relation = tUnbounded;
          placement = mergeAtRoot;
        }
      );
      # ONE RESPECT ALTERED: it drops an entry, which a rendering may never do.
      mutant = [
        (v.renderEntry (
          builtins.head (
            v.trace {
              relation = tUnbounded;
              placement = mergeAtRoot;
            }
          )
        ))
      ];
    };

    # RENDER-ENTRY: the per-entry half, carrying target, source, witness word and mode.
    renderEntry = {
      capability = s: s == "root:inc/settings ← inc/import [include] d=1 merge";
      fixture = v.renderEntry (entryOf mergeAtRoot);
      # ONE RESPECT ALTERED: the mode, which the rendering must carry.
      mutant = v.renderEntry (entryOf nestAtRoot);
    };

    # TRACE-ENTRY-OF: the structured identity entry — IDENTITY ONLY, NEVER RESOLVED CONTENT.
    traceEntryOf = {
      capability =
        e:
        !(e ? datum)
        &&
          builtins.attrNames e == [
            "distance"
            "kind"
            "mode"
            "path"
            "source"
            "target"
            "word"
          ];
      fixture = entryOf mergeAtRoot;
      # ONE RESPECT ALTERED: the entry carries the resolved content, which is what makes a trace
      # force what it was built not to force.
      mutant = (entryOf mergeAtRoot) // {
        datum = (builtins.head f.relation.contributions).datum;
      };
    };

    # EDGE-SORT-KEY: the frozen `T | P | S | M [| K]` key.
    edgeSortKey = {
      capability = k: k == "root:inc/settings | cfg | inc/import | merge | import";
      fixture = v.edgeSortKey (entryOf mergeAtRoot);
      # ONE RESPECT ALTERED: the M component.
      mutant = v.edgeSortKey (entryOf nestAtRoot);
    };
  };

  names = builtins.attrNames cases;

  expressibleCells = builtins.listToAttrs (
    map (n: {
      name = "test-${n}-is-expressible-and-asserted";
      value = {
        expr = cases.${n}.capability cases.${n}.fixture;
        expected = true;
      };
    }) names
  );

  mutantCells = builtins.listToAttrs (
    map (n: {
      name = "test-control-${n}-assertion-rejects-its-mutant";
      value = {
        expr = cases.${n}.capability cases.${n}.mutant;
        expected = false;
      };
    }) names
  );
in
{
  flake.tests.exports =
    expressibleCells
    // mutantCells
    // {
      # ★ THE ROSTER IS THE CHECKED ARTEFACT. An export dropped from this table takes its two cells
      # with it silently; this cell is what refuses that. It is the export map's own sixteen, by name.
      test-control-the-sixteen-exports-are-all-covered = {
        expr = names;
        expected = [
          "channel"
          "compose"
          "defaultFold"
          "edge"
          "edgeSortKey"
          "edgesFor"
          "materialize"
          "project"
          "renderEntry"
          "renderTrace"
          "run"
          "sources"
          "targets"
          "trace"
          "traceEntryOf"
          "traceOf"
        ];
      };

      # And every case really carries all three parts — a case with a missing mutant would generate a
      # cell that evaluated `capability null` and could pass for the wrong reason.
      test-control-every-case-carries-a-capability-a-fixture-and-a-mutant = {
        expr = builtins.all (
          n: builtins.isFunction cases.${n}.capability && cases.${n} ? fixture && cases.${n} ? mutant
        ) names;
        expected = true;
      };
    };
}
