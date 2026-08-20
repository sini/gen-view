# ORACLE O7 — ARRIVAL MODE IS DERIVABLE, AND A WALK-EMITTED VALUE'S PARTICIPATION IS
# INEXPRESSIBLE.
#
# ★★★ THE NEGATIVE ARM IS A HAND-CONSTRUCTED ADVERSARIAL FIXTURE, AND IT HAS TO BE. The property
# this preserves IS ALREADY TRUE of the ecosystem — measured, there is no mechanical re-emission
# channel anywhere in the gen family, so every contribution is already authored. A negative arm
# with no subject passes VACUOUSLY FOREVER, which is why the fixture below reproduces the shape by
# hand rather than looking for one:
#
#   a scope whose data component MECHANICALLY RE-EMITS the host's channel-named keys by walking out
#   of itself, so the re-emitted value sits at DISTANCE 0 and would beat the host's own value at
#   DISTANCE 1.
#
# The oracle asserts the re-emitted value DOES NOT COMPETE.
#
# ★★ TWO CONTROLS, BOTH ABLE TO FAIL:
#   (i)  THE POSITIVE — the SAME value AUTHORED at the SAME position DOES compete and appears in
#        the result. Nothing is lost: the semantics stays fully available to an author who writes
#        the value down; what dies is the implicit side effect, never the semantics it produced.
#   (ii) THE VACUITY CHECK — the fixture must be shown to construct a GENUINELY walk-emitted value.
#        Removing the discriminator makes the fixture's value appear: `emittedAt` is the
#        undiscriminated reading and it HAS the datum, `authoredAt` is the discriminated one and it
#        does not. Without (ii) a passing negative arm is indistinguishable from a fixture that
#        never built its subject.
#
# ★★ WHY THE DISCRIMINATOR IS DERIVABLE AT ALL, WHICH IS THE WHOLE GROUND. The defect was never an
# intent — it was a MECHANICAL RE-EMISSION, a structural fact about HOW THE VALUE ARRIVED rather
# than a fact about what anyone meant. A contribution's SORT is derivable; its INTENT is not; this
# asks only for the former. So no declaration is involved, and the standing rule that a dependence
# fact is DERIVED unless derivation is proven impossible is unbroken.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  labels = v.edgeLabels { letters = [ "parent" ]; };
  relations = v.relations { names = [ "import" ]; };
  admission = v.labelWellFormedness {
    alphabet = labels;
    expression = "parent*";
  };
  order = v.labelOrder {
    alphabet = labels;
    layers = [ [ "parent" ] ];
    endOfPath = -1;
  };
  key = v.dataOrder {
    channel = "settings";
    keyOf = _: "settings";
  };
  carrier = v.carrier {
    inherit labels relations;
    relatumLabels = f.roles;
    labelWellFormedness = admission;
    labelOrder = order;
    dataOrder = key;
  };

  scopes = [
    "host"
    "child"
  ];
  edges = {
    parent = id: if id == "child" then [ "host" ] else [ ];
  };

  hostDatum = {
    relation = "import";
    datum = [ "host-assembled" ];
  };

  # ── THE ADVERSARIAL FIXTURE ──
  # `child`'s data component is a function OF THE GRAPH, and it uses that: it walks out of itself
  # and re-emits, AT ITSELF, whatever the host holds. That is v1's arm-F shape in miniature — a
  # node walk re-emitting a host aspect's channel-named keys.
  reEmitting =
    labeled: scope:
    let
      own = if scope == "host" then [ hostDatum ] else [ ];
      reEmitted = builtins.concatMap (e: if e.target == "host" then [ hostDatum ] else [ ]) (
        labeled.labeledEdges scope
      );
    in
    own ++ reEmitted;

  adversarial = v.scopeGraph {
    inherit carrier scopes edges;
    data = reEmitting;
  };

  # ── THE POSITIVE ARM'S FIXTURE ──
  # The same datum, at the same position, AUTHORED: the data component ignores the graph entirely.
  authoredEverywhere = _: _: [ hostDatum ];
  authored = v.scopeGraph {
    inherit carrier scopes edges;
    data = authoredEverywhere;
  };

  definition = v.compositions.movement {
    channel = "settings";
    relation = "import";
    root = "child";
    direction = "outbound";
    inherit admission order;
    wellFormed = f.admitAll;
    tieSet = v.tieSets.union;
    empty = [ ];
    combine = v.combines.listAppend;
    dedup = v.dedups.none;
  };

  relationOver =
    g:
    v.viewRelation {
      inherit definition;
      graph = g;
      marks = f.noMarks;
    };
in
{
  flake.tests.arrival = {
    # ── THE NEGATIVE ARM: THE RE-EMITTED VALUE DOES NOT COMPETE ──
    # It would have arrived at `child`, at distance 0, and beaten the host's own at distance 1. The
    # only contribution in the result is the host's.
    test-a-walk-emitted-value-does-not-compete = {
      expr = map (c: {
        inherit (c) scope distance;
      }) (relationOver adversarial).contributions;
      expected = [
        {
          scope = "host";
          distance = 1;
        }
      ];
    };

    # ★★ (ii) THE VACUITY CHECK — the fixture BUILT ITS SUBJECT. The undiscriminated reading has
    # the datum at `child`; the discriminated one does not. If these two agreed, the negative arm
    # above would be passing on a fixture that never re-emitted anything.
    test-control-the-adversarial-fixture-really-emits-a-walk-emitted-value = {
      expr = {
        undiscriminated = v.emittedAt adversarial "child";
        discriminated = v.authoredAt adversarial "child";
      };
      expected = {
        undiscriminated = [ hostDatum ];
        discriminated = [ ];
      };
    };

    # And the discriminator SAYS SO, by name, on the same entry.
    test-the-discriminator-classifies-the-re-emitted-value = {
      expr = v.arrivalMode {
        graph = adversarial;
        scope = "child";
        entry = hostDatum;
      };
      expected = "walk-emitted";
    };

    # ★★ (i) THE POSITIVE ARM — the SAME value AUTHORED at the SAME position DOES compete, and
    # wins, because its empty path beats the host's. NOTHING IS LOST: the semantics is available to
    # an author who writes the value down, and only the accident is gone.
    test-control-the-same-value-authored-at-the-same-position-does-compete = {
      expr = {
        contributions = map (c: {
          inherit (c) scope distance;
        }) (relationOver authored).contributions;
        mode = v.arrivalMode {
          graph = authored;
          scope = "child";
          entry = hostDatum;
        };
      };
      expected = {
        contributions = [
          {
            scope = "child";
            distance = 0;
          }
        ];
        mode = "authored";
      };
    };

    # ── THE MECHANISM: SEVERING A SCOPE'S OUT-EDGES IS THE WHOLE OF THE INTERVENTION ──
    # In the calculus, `data(G)` is a COMPONENT of the graph and is walk-independent by definition.
    # Severing the scope's out-edges removes exactly the walk a re-emitting accessor consults and
    # nothing else — the node set is untouched — so what survives is the component in the
    # calculus's own sense.
    test-severing-a-scopes-out-edges-leaves-the-node-set-intact = {
      expr =
        let
          severed = v.severedAt adversarial.labeled "child";
        in
        {
          nodes = severed.nodes;
          childHasNoEdges = severed.labeledEdges "child" == [ ];
          hostIsUntouched = severed.labeledEdges "host" == adversarial.labeled.labeledEdges "host";
        };
      expected = {
        nodes = [
          "host"
          "child"
        ];
        childHasNoEdges = true;
        hostIsUntouched = true;
      };
    };

    # ★ THE ORDINARY CASE PAYS NO SEMANTIC PRICE. An accessor that ignores the graph — which is
    # what an authored data component is — answers identically under both readings, so the
    # discriminator is invisible to every graph that was not trying to re-emit.
    test-control-an-authored-component-reads-the-same-either-way = {
      expr = {
        emitted = v.emittedAt f.graph "mid";
        authored = v.authoredAt f.graph "mid";
      };
      expected = {
        emitted = [
          {
            relation = "import";
            datum = [ "mid" ];
          }
        ];
        authored = [
          {
            relation = "import";
            datum = [ "mid" ];
          }
        ];
      };
    };

    # ── A DATUM THAT IS AT NEITHER READING HAS NO ARRIVAL MODE, AND IS REFUSED ──
    # Answering "walk-emitted" for a datum that is simply not there would let a caller's typo
    # report a structural finding. The mode is a question about a datum that has arrived.
    test-an-absent-datum-has-no-arrival-mode = {
      expr =
        !(builtins.tryEval (
          v.arrivalMode {
            graph = adversarial;
            scope = "child";
            entry = {
              relation = "import";
              datum = [ "never-filed" ];
            };
          }
        )).success;
      expected = true;
    };

    # ── THE TWO MODES ARE THE PUBLISHED ENUMERATION ──
    # There is no third: a datum is in the walk-independent component or it is not.
    test-control-the-arrival-modes-are-exactly-two = {
      expr = v.arrivalModes;
      expected = [
        "authored"
        "walk-emitted"
      ];
    };

    # ── THE CONSTRUCTION THE RULING SAYS MUST NOT BE LIMITED ──
    # A SELF-EDGE used to gather a facet is measured safe: facet collection is the BASE TERM of a
    # union with a SELF-EXCLUDING gather, so it never enters the gather and never competes.
    # Severing a scope's out-edges does not touch it, and here the self-edge graph still answers.
    test-a-self-excluding-facet-gather-is-unaffected = {
      expr =
        let
          selfEdged = v.scopeGraph {
            inherit carrier;
            scopes = [ "host" ];
            edges = {
              parent = _: [ "host" ];
            };
            data = authoredEverywhere;
          };
        in
        map
          (c: {
            inherit (c) scope distance;
          })
          (v.viewRelation {
            definition = v.compositions.movement {
              channel = "settings";
              relation = "import";
              root = "host";
              direction = "outbound";
              inherit admission order;
              wellFormed = f.admitAll;
              tieSet = v.tieSets.union;
              empty = [ ];
              combine = v.combines.listAppend;
              dedup = v.dedups.none;
            };
            graph = selfEdged;
            marks = f.noMarks;
          }).contributions;
      expected = [
        {
          scope = "host";
          distance = 0;
        }
      ];
    };
  };
}
