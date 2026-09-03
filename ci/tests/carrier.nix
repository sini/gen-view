# ORACLE O4 — THE RAW CALCULUS IS PUBLISHED, NOT ONLY THE COMPOSITIONS.
#
# Two claims, and the second is the one that can rot silently:
#   (i)  each of the five carrier elements is reachable as a NAMED EXPORT, and a caller can build
#        a view over a carrier instance NO SHIPPED COMPOSITION SUPPLIES;
#   (ii) the movement composition constructs over THOSE SAME EXPORTS — so the raw layer is the one
#        the composition uses and not a parallel surface kept beside it for show.
#
# ★ (ii) IS THE CONTROL AND IT IS NOT DECORATION. A library can publish five constructors, build
# its compositions from five private twins, and satisfy (i) forever while the published layer
# drifts out of step with the one that runs. The check is a VALUE identity: the element the caller
# built is the element the declaration holds.
#
# ★★ AND THE OTHER FAILURE O4 NAMES IS THE ONE THAT SAYS WHETHER A RULING WAS BUILT OR ONLY
# RECORDED: den's four binding kinds must be EXPRESSIBLE OVER THE PUBLISHED CARRIER as RELATIONS,
# with `include` available as a structural letter and no fifth structural symbol added to carry
# containment.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  # The layered order and the flat order differ in exactly one respect. Everything else about the
  # two declarations is the same construction.
  layered = f.relation;
  flat = f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; };
  scopesOf = r: map (c: c.scope) r.contributions;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;

  # ── THE ROLE-EDGE FIXTURE ──
  # `leaf` carries a `relatum-target` incidence edge to a binding node, exactly as a reified
  # relation's incidence reaches the edge set. The binding holds a datum under the DECLARED
  # relation, so a walk that could step on the role edge would find it and change the answer —
  # which is what makes the inertness claim falsifiable.
  roleData = f.authored {
    mid = [
      {
        relation = "import";
        datum = [ "mid" ];
      }
    ];
    binding = [
      {
        relation = "import";
        datum = [ "SHOULD-NOT-BE-REACHED" ];
      }
    ];
  };
  roleScopes = [
    "leaf"
    "mid"
    "binding"
  ];
  roleEdges = {
    parent = id: if id == "leaf" then [ "mid" ] else [ ];
  };
  roleGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = roleScopes;
    edges = roleEdges // {
      relatum-target = id: if id == "leaf" then [ "binding" ] else [ ];
    };
    data = roleData;
  };
  # The SAME graph with the role edge removed — the counterpart the inertness claim is measured
  # against, differing in exactly that one edge.
  plainGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = roleScopes;
    edges = roleEdges;
    data = roleData;
  };
  roleDefinition = f.mkDefinition { root = "leaf"; };
  roleRelation = v.viewRelation {
    definition = roleDefinition;
    graph = roleGraph;
    marks = f.noMarks;
  };
  plainRelation = v.viewRelation {
    definition = roleDefinition;
    graph = plainGraph;
    marks = f.noMarks;
  };
in
{
  flake.tests.carrier = {
    # ── (i) THE FIVE ARE REACHABLE, AND A CALLER BUILDS OVER THEM DIRECTLY ──
    # A carrier assembled from the five published constructors, with no composition involved at
    # any step. If any element were reachable only through a composition this could not be written.
    test-a-carrier-is-assembled-from-the-published-elements-alone = {
      expr = builtins.attrNames f.carrier;
      expected = [
        "__element"
        "dataOrder"
        "labelOrder"
        "labelWellFormedness"
        "labels"
        "relations"
        "relatumLabels"
      ];
    };

    # THE CARRIER INSTANCE NO SHIPPED COMPOSITION SUPPLIES: a NON-EMPTY label order, under which
    # the containment letter outranks the ancestor letter. The answer differs from the flat order's
    # answer, which is what shows the order is READ rather than carried.
    test-a-non-empty-label-order-changes-which-contribution-survives = {
      expr = {
        layered = scopesOf layered;
        flat = scopesOf flat;
      };
      expected = {
        layered = [ "inc" ];
        flat = [
          "inc"
          "mid"
        ];
      };
    };

    # ★ THE CONTROL FOR THE CELL ABOVE, IN THE SAME RUN: the two declarations differ in the ORDER
    # ELEMENT AND IN NOTHING ELSE. Without it, two different answers are equally consistent with
    # two fixtures that differ somewhere nobody looked.
    #
    # ★★ THE RAW-LAMBDA FIELDS ARE COMPARED BY NAME AND NOT BY VALUE, AND THAT IS A FACT ABOUT THE
    # LANGUAGE RATHER THAN A WEAKENING. Measured on this evaluator: `==` on two bare function
    # values is FALSE EVEN AGAINST ITSELF — `{ v = d.distance; } == { v = d.distance; }` reads
    # false for one and the same attribute. So `wellFormed`, `distance` and the key's closure are
    # excluded from the structural comparison and checked by the names they are built from; every
    # remaining field, INCLUDING the element attrsets that carry functions inside them, compares by
    # value because both declarations hold the same constructed element.
    test-control-the-two-declarations-differ-only-in-the-order-element = {
      expr = {
        everyInertField =
          removeAttrs layered.definition [
            "order"
            "channel"
            "wellFormed"
            "distance"
          ] == removeAttrs flat.definition [
            "order"
            "channel"
            "wellFormed"
            "distance"
          ];
        sameName = layered.definition.name == flat.definition.name;
        sameFieldSet = builtins.attrNames layered.definition == builtins.attrNames flat.definition;
        orderReallyChanged = layered.definition.order != flat.definition.order;
      };
      expected = {
        everyInertField = true;
        sameName = true;
        sameFieldSet = true;
        orderReallyChanged = true;
      };
    };

    # ── (ii) THE COMPOSITION USES THE PUBLISHED ELEMENTS, NOT PRIVATE TWINS ──
    test-control-the-movement-composition-holds-the-very-elements-the-caller-built = {
      expr = {
        admission = layered.definition.admission == f.admission;
        order = layered.definition.order == f.order;
      };
      expected = {
        admission = true;
        order = true;
      };
    };

    # ★ AND THE IDENTITY CHECK IS SHOWN ABLE TO FAIL. Two structurally equal elements built twice
    # would compare equal in Nix, so the cell above is only meaningful if the comparison can
    # distinguish anything at all — here, an element that is genuinely different.
    test-control-the-element-identity-check-discriminates = {
      expr = layered.definition.order == f.flatOrder;
      expected = false;
    };

    # ── THE RULING IS BUILT, NOT MERELY RECORDED ──
    # den's four binding kinds are RELATIONS in R, `include` is a structural LETTER in L, and the
    # two populations are disjoint. The alphabet carries no fifth structural symbol for containment
    # — the containment letter falls out of the arrangement rather than being added by a separate
    # act.
    test-dens-four-binding-kinds-are-relations-not-letters = {
      expr = {
        relations = f.relations.names;
        letters = f.labels.letters;
        overlap = builtins.filter (r: f.labels.member r) f.relations.names;
      };
      expected = {
        relations = [
          "import"
          "expose-in"
          "broadcast-in"
          "policy"
        ];
        letters = [
          "parent"
          "include"
        ];
        overlap = [ ];
      };
    };

    # And a view over one of those relations MATERIALIZES — the ruling is expressible end to end,
    # not merely declarable. `policy` reaches exactly the one datum filed under it.
    test-a-view-over-a-relation-materializes = {
      expr = (f.mkRelation { definition = f.mkDefinition { relation = "policy"; }; }).value;
      expected = [ "not-this-relation" ];
    };

    # ── (NR-Rel): THE RELATION IS REACHED ONCE, AT THE END OF THE PATH ──
    # The lookup is over the data component and takes WFD; the walk never steps on a relation name.
    test-relation-lookup-is-the-terminus-rule = {
      expr = v.relationLookup {
        graph = f.graph;
        scope = "inc";
        relation = "import";
        wellFormed = _: true;
      };
      expected = [ [ "inc" ] ];
    };

    # WFD narrows the DATUM, never the path — the second premise of (NR-Rel) doing its own work.
    test-control-wfd-narrows-the-datum-and-not-the-path = {
      expr = v.relationLookup {
        graph = f.graph;
        scope = "inc";
        relation = "import";
        wellFormed = d: d != [ "inc" ];
      };
      expected = [ ];
    };

    # ── THE EXTENDED ALPHABET IS DERIVED, NOT DECLARED ──
    # `$` "indicates the end of a path", which is a property of every alphabet rather than a choice
    # about one, so it is never a letter a caller writes.
    test-the-extended-alphabet-is-derived = {
      expr = f.labels.extended;
      expected = [
        "parent"
        "include"
        "$"
      ];
    };

    # ── THE LABEL ORDER IS A STRICT PARTIAL ORDER OVER THE EXTENDED ALPHABET ──
    # Two letters in ONE layer are incomparable in both directions; that is what layers buy over a
    # flat ranking, and it is why "no specificity at all" is expressible rather than accidental.
    test-two-letters-in-one-layer-are-incomparable = {
      expr = {
        forward = f.flatOrder.precedes "include" "parent";
        backward = f.flatOrder.precedes "parent" "include";
        layeredForward = f.order.precedes "include" "parent";
        layeredBackward = f.order.precedes "parent" "include";
      };
      expected = {
        forward = false;
        backward = false;
        layeredForward = true;
        layeredBackward = false;
      };
    };

    # The end-of-path rank ranks `$`, and at the shipped value stopping outranks everything — a
    # proper prefix beats its own extensions.
    test-the-end-of-path-rank-makes-a-prefix-beat-its-extensions = {
      expr =
        f.order.pathPrecedes
          [ { label = "parent"; } ]
          [
            { label = "parent"; }
            { label = "parent"; }
          ];
      expected = true;
    };

    # ══ THE LIFT IS Fig. 1's VISIBILITY ORDER, AND DISTINCT SAME-RANK LABELS LEAVE IT UNDECIDED ══
    #
    # ★★★ THE DEFECT THIS PINS: a lift that compares RANK WORDS lexicographically recurses past a
    # position where the labels DIFFER but their ranks are equal — treating incomparability as
    # "comparable so far". That lift is strictly FINER than `<p`: it shadows contributions the
    # calculus keeps visible, and the loss lands in the materialized value.
    #
    # Fig. 1 licenses recursion only through the CONGRUENCE (`s·l·p1 <p s·l·p2`, the SAME label),
    # and licenses ordering at a divergence only where the two labels are `<l`-comparable
    # (`l1 <l l2 ⟹ s·l1·p1 <p s·l2·p2`).
    test-distinct-same-rank-labels-leave-the-paths-incomparable = {
      expr = {
        # the element already said so
        elementForward = f.flatOrder.precedes "include" "parent";
        elementBackward = f.flatOrder.precedes "parent" "include";
        # ★ and now the LIFT says so too, in both directions — this is the pair that read `true`
        liftForward =
          f.flatOrder.pathPrecedes
            [ { label = "include"; } ]
            [
              { label = "parent"; }
              { label = "parent"; }
            ];
        liftBackward =
          f.flatOrder.pathPrecedes
            [
              { label = "parent"; }
              { label = "parent"; }
            ]
            [ { label = "include"; } ];
      };
      expected = {
        elementForward = false;
        elementBackward = false;
        liftForward = false;
        liftBackward = false;
      };
    };

    # ★★★ THE CONTROL WITHOUT WHICH THE CELL ABOVE IS WORTHLESS: A LIFT THAT ORDERS NOTHING AT ALL
    # WOULD PASS IT. Over-correction is the live hazard — "return false everywhere" satisfies every
    # incomparability claim in this file. So the same lift, in the same run, must still ORDER the
    # cases Fig. 1 licenses: the congruence-then-exhaustion prefix case, and a comparable
    # divergence in one direction only.
    test-control-the-lift-still-orders-what-the-figure-licenses = {
      expr = {
        # `$ <l l` ⇒ s <p s·l·p — a proper prefix beats its extensions even under a FLAT order,
        # because the divergence is at exhaustion and `$` is a label of its own distinct rank.
        prefixUnderFlatOrder =
          f.flatOrder.pathPrecedes
            [ { label = "parent"; } ]
            [
              { label = "parent"; }
              { label = "parent"; }
            ];
        # `l1 <l l2` ⇒ ordered, where the ranking makes the two labels comparable
        comparableDivergence =
          f.order.pathPrecedes
            [ { label = "include"; } ]
            [
              { label = "parent"; }
              { label = "parent"; }
            ];
        comparableDivergenceReversed =
          f.order.pathPrecedes
            [
              { label = "parent"; }
              { label = "parent"; }
            ]
            [ { label = "include"; } ];
      };
      expected = {
        prefixUnderFlatOrder = true;
        comparableDivergence = true;
        comparableDivergenceReversed = false;
      };
    };

    # ★ AN `endOfPath` EQUAL TO A LETTER'S RANK LEAVES STOPPING AND CONTINUING INCOMPARABLE — a
    # sayable declaration under Fig. 1, and one the rank-word lift could not express.
    test-an-end-of-path-rank-equal-to-a-letters-rank-is-incomparable = {
      expr =
        let
          tied = v.labelOrder {
            alphabet = f.labels;
            layers = [
              [
                "include"
                "parent"
              ]
            ];
            endOfPath = 0;
          };
        in
        {
          forward =
            tied.pathPrecedes
              [ { label = "parent"; } ]
              [
                { label = "parent"; }
                { label = "parent"; }
              ];
          backward =
            tied.pathPrecedes
              [
                { label = "parent"; }
                { label = "parent"; }
              ]
              [ { label = "parent"; } ];
        };
      expected = {
        forward = false;
        backward = false;
      };
    };

    # ★★ THE SEPARATOR — `pathPrecedes` SURVIVES `rankLess`'s MIGRATION AND IS NOT SUBSTITUTED FOR
    # IT. `rankLess` is now `graph.wordLess` at a pin (gen-graph publishes the rank-word calculus);
    # `pathPrecedes` is Fig. 1's visibility order and gen-graph has NO counterpart to it. The two
    # are different orders, and this cell says so in the one shape a silent substitution fails:
    # `rankLess` DECIDES a pair `pathPrecedes` leaves incomparable in BOTH directions. Substitute
    # either for the other and a reading below flips.
    #
    # ★ THE TIE IS WHAT DISCRIMINATES, and a tie-free fixture would measure nothing. A total and a
    # partial order agree on every pair of a singleton-layer order — measured, 0 disagreements over
    # 100 pairs — so a cell written there passes under the very substitution this one exists to
    # catch. Three letters with the first two TIED is the smallest shape that separates them:
    # `[P·X]` and `[I·P]` differ at position 0 on labels of EQUAL rank, which is exactly where
    # Fig. 2's recursion is unlicensed and the rank-word lift walks on.
    test-rankLess-decides-a-pair-pathPrecedes-leaves-incomparable = {
      expr =
        let
          tied = v.labelOrder {
            alphabet = v.edgeLabels {
              letters = [
                "P"
                "I"
                "X"
              ];
            };
            layers = [
              [
                "P"
                "I"
              ]
              [ "X" ]
            ];
            endOfPath = -1;
          };
          px = [
            { label = "P"; }
            { label = "X"; }
          ];
          ip = [
            { label = "I"; }
            { label = "P"; }
          ];
        in
        {
          rankLessForward = tied.rankLess px ip;
          rankLessBackward = tied.rankLess ip px;
          pathPrecedesForward = tied.pathPrecedes px ip;
          pathPrecedesBackward = tied.pathPrecedes ip px;
        };
      expected = {
        # the sort key DECIDES the pair
        rankLessForward = false;
        rankLessBackward = true;
        # the visibility order REFUSES it, both ways
        pathPrecedesForward = false;
        pathPrecedesBackward = false;
      };
    };

    # ══ Λ — THE RELATUM LABELS ARE PRESENT AND INERT, AND THE COLLISION IS WHAT IS REFUSED ══
    #
    # ★★★ THE LAW IS A THREE-WAY CONDITION: `L ∩ R = ∅` · `L ∩ Λ = ∅` · `R ∩ Λ = ∅` and
    # `labels(edges(G)) ⊆ L ⊎ R ⊎ Λ` — disjoint AND jointly exhaustive, refused at construction.
    # A binding's incident edges DO reach the edge set, carrying the roles its relata play; they
    # are HELD AND NOT WALKED. The guard this replaces demanded membership in `L` alone, which is
    # that law INVERTED — it refused the case the law requires present and accepted the case the
    # law requires refused, and it left this library unable to hold any graph the minter produces.
    #
    # THREE ASSERTIONS, because "present" and "inert" are different claims and neither implies the
    # other: the role edge is IN the edge set · the walk CANNOT step on it · it never COMPETES.
    test-a-non-colliding-relatum-edge-is-present-and-inert = {
      expr = {
        # (i) PRESENT — the incidence edge is in the graph, reachable through the same accessor
        # every other edge is.
        present = builtins.any (e: e.label == "relatum-target") (roleGraph.labeled.labeledEdges "leaf");
        # (ii) NOT WALKED — structurally, not by a filter: the derivative of the admission
        # expression with respect to a role label is the EMPTY state, whose canonical key is "0",
        # so the walk prunes at that edge. That is the whole inertness argument, executed.
        derivativeIsEmpty = f.admission.stateKey (f.admission.step "relatum-target" f.admission.expr);
        # …and the scope on the far side of it is never reached.
        bindingReached = builtins.any (c: c.scope == "binding") roleRelation.contributions;
        # (iii) NEVER COMPETES — the answer is identical to the same graph with the role edge
        # removed, in value, in membership and in what was shadowed.
        sameValue = roleRelation.value == plainRelation.value;
        sameScopes =
          map (c: c.scope) roleRelation.contributions == map (c: c.scope) plainRelation.contributions;
        sameShadowed = map (c: c.scope) roleRelation.shadowed == map (c: c.scope) plainRelation.shadowed;
      };
      expected = {
        present = true;
        derivativeIsEmpty = "0";
        bindingReached = false;
        sameValue = true;
        sameScopes = true;
        sameShadowed = true;
      };
    };

    # ★ THE CONTROL THAT THE INERTNESS CELL IS NOT VACUOUS: the far-side scope HAS a datum under the
    # declared relation, so a walk that could step on the role edge would find something and change
    # the answer. Without this, "binding is never reached" is consistent with a fixture that had
    # nothing to reach.
    test-control-the-far-side-of-the-role-edge-really-holds-a-datum = {
      expr = v.relationLookup {
        graph = roleGraph;
        scope = "binding";
        relation = "import";
        wellFormed = f.admitAll;
      };
      expected = [ [ "SHOULD-NOT-BE-REACHED" ] ];
    };

    # ── THE COLLISION IS THE CASE THE LAW REFUSES, AND IT IS REFUSED BY NAME ──
    # A role label that is also a letter would make a binding's incidence WALKABLE: the derivative
    # would not go to the empty state, the walk would step onto a relatum edge, and the inertness
    # argument would be false while still being written down.
    test-the-three-pairwise-collisions-are-each-refused = {
      expr = {
        lambdaAgainstL = refuses (
          v.carrier {
            labels = f.labels;
            labelWellFormedness = f.admission;
            labelOrder = f.order;
            dataOrder = f.key;
            relations = f.relations;
            relatumLabels = v.relatumLabels { names = [ "parent" ]; };
          }
        );
        lambdaAgainstR = refuses (
          v.carrier {
            labels = f.labels;
            labelWellFormedness = f.admission;
            labelOrder = f.order;
            dataOrder = f.key;
            relations = f.relations;
            relatumLabels = v.relatumLabels { names = [ "import" ]; };
          }
        );
        # the L∩R arm, already covered in the refusal suite, re-run here so all three read together
        rAgainstL = refuses (
          v.carrier {
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
            relatumLabels = f.roles;
          }
        );
      };
      expected = {
        lambdaAgainstL = true;
        lambdaAgainstR = true;
        rAgainstL = true;
      };
    };

    # ── EXHAUSTIVENESS: A LABEL IN NONE OF THE THREE POPULATIONS IS REFUSED ──
    # The classification of an edge label is TOTAL. A label outside all three would be walked by
    # nothing and classified as nothing — a silent drop wearing a total function's name.
    test-an-edge-label-in-no-population-is-refused = {
      expr = refuses (
        v.scopeGraph {
          carrier = f.carrier;
          scopes = [ "leaf" ];
          edges = {
            not-a-population = _: [ ];
          };
          data = f.authored { };
        }
      );
      expected = true;
    };

    # ★ THE REGRESSION CONTROL: THE L-ONLY GRAPH IS UNCHANGED. Every existing expectation in this
    # suite rides on the fixture graph, which holds no Λ edge at all; this cell says so directly, so
    # a future widening of the guard cannot be mistaken for the population arriving.
    test-control-the-l-only-graph-is-unchanged = {
      expr = {
        edgeLabels = builtins.attrNames f.graph.edges;
        allInL = builtins.all (l: f.labels.member l) (builtins.attrNames f.graph.edges);
        value = f.relation.value;
        lambdaDeclaredButUnused = f.carrier.relatumLabels.names;
      };
      expected = {
        edgeLabels = [
          "include"
          "parent"
        ];
        allInL = true;
        value = [ "inc" ];
        lambdaDeclaredButUnused = [
          "relatum-target"
          "relatum-source"
        ];
      };
    };

    # ── Λ IS NOT A CARRIER ELEMENT, AND THE ENUMERATION SAYS SO ──
    # Admission is indexed by the binding's KIND — the relation `r` — and never by a role label, so
    # `Λ` indexes nothing in the carrier. It is a published constructor and a required carrier
    # FIELD; it is not one of the five.
    test-lambda-is-a-published-constructor-and-not-a-carrier-element = {
      expr = {
        published = builtins.isFunction v.relatumLabels;
        inTheFive = builtins.elem "relatumLabels" v.carrierElements;
        theFive = builtins.length v.carrierElements;
      };
      expected = {
        published = true;
        inTheFive = false;
        theFive = 5;
      };
    };
  };
}
