# A FUNCTION AN ELEMENT CARRIES IS NEVER TRUSTED FOR ITS RESULT (den-hoag-l83dk; p79do Q1: a tag is
# a CLAIM). Every function-typed field of every element shape (`elements.shapes`, the register the
# intake re-checks against) is classified here, and the census cell holds the classification equal
# to the register, so a function field added to a shape without a disposition reds this file.
#
#   restated   the library derives the operation from the element's checked structure and never
#              applies the field (`member` from `letters`/`names`, `step`/`stateKey` from gen-graph's
#              regex kernel over `expr`), so a forged result is INERT: the read equals the genuine one.
#   checked    the library applies the field and checks its result by name where it is consumed.
#   unapplied  nothing in the library applies the field; it is published for callers.
#   content    the result IS the answer (a datum, a dedup key); no check of the library's reads it.
#
# ★ RESTATED IS ONLY AS GOOD AS WHAT IT READS. `member` is restated from `letters`/`names`, so those
# lists are checked at intake by their constructor's own law (elements.nix `lettersLaw` and its two
# siblings), and the `refused-list` cells hold that: a forged list the constructor refuses is refused
# by name at every door that reads it, and a forged `member` cannot hide a collision the list states.
#
# On `testsError` for the reason `forged-intake.nix` states: before this landing a forged result
# aborted past `tryEval`, which the batch asserter behind `checks.default` would crash on.
{
  genView,
  genPrelude,
  ...
}:
let
  v = genView;
  f = import ./fixture.nix { inherit genView; };
  inherit (import ../lib/elements.nix { prelude = genPrelude; }) shapes;

  read = rel: {
    inherit (rel)
      value
      contributions
      dropped
      shadowed
      withheld
      ;
  };
  genuineRead = read f.relation;
  viaDef = over: read (f.mkRelation { definition = f.definition // over; });
  viaGraph = g: read (f.mkRelation { graph = g; });
  carrierArgs = {
    inherit (f) labels relations;
    relatumLabels = f.roles;
    labelWellFormedness = f.admission;
    labelOrder = f.order;
    dataOrder = f.key;
  };
  graphOver =
    c: extraEdges:
    v.scopeGraph {
      carrier = c;
      inherit (f) scopes;
      edges = f.edges // extraEdges;
      data = f.authored f.datums;
    };
  forty2 = _: 42;
  badLabels = f.labels // {
    member = forty2;
  };
  badRels = f.relations // {
    member = forty2;
  };
  badRoles = f.roles // {
    member = forty2;
  };
  # an alphabet forged at `member` only, carried by every element built over L
  admissionOver =
    labels:
    v.labelWellFormedness {
      alphabet = labels;
      expression = "(parent|include)*";
    };
  orderOver =
    labels:
    v.labelOrder {
      alphabet = labels;
      layers = [
        [ "include" ]
        [ "parent" ]
      ];
      endOfPath = -1;
    };
  carrierOverLabels =
    labels:
    v.carrier (
      carrierArgs
      // {
        inherit labels;
        labelWellFormedness = admissionOver labels;
        labelOrder = orderOver labels;
      }
    );
  relOverLabels =
    labels:
    read (
      f.mkRelation {
        definition = f.mkDefinition {
          admission = admissionOver labels;
          order = orderOver labels;
        };
        graph = graphOver (carrierOverLabels labels) { };
      }
    );

  # the Λ-edge graph: `unclassified` reaches `relatumLabels` only for a label outside L and R
  roleEdge = {
    relatum-target = _: [ ];
  };

  disposition = {
    "edgeLabels.member" = "restated";
    "relations.member" = "restated";
    "relatumLabels.member" = "restated";
    "labelWellFormedness.step" = "restated";
    "labelWellFormedness.stateKey" = "restated";
    "labelOrder.rankOf" = "checked";
    "dataOrder.keyOf" = "checked";
    "viewDefinition.wellFormed" = "checked";
    "viewDefinition.distance" = "checked";
    "labelWellFormedness.accepts" = "unapplied";
    "labelOrder.precedes" = "unapplied";
    "labelOrder.rankWord" = "unapplied";
    "labelOrder.pathPrecedes" = "unapplied";
    "labelOrder.rankLess" = "unapplied";
    "combine.op" = "content";
    "dedup.keyOf" = "content";
  };

  genuine = {
    edgeLabels = f.labels;
    relations = f.relations;
    relatumLabels = f.roles;
    labelWellFormedness = f.admission;
    labelOrder = f.order;
    dataOrder = f.key;
    carrier = f.carrier;
    scopeGraph = f.graph;
    tieSet = v.tieSets.union;
    combine = v.combines.listAppend;
    dedup = v.dedups.byKey { keyOf = c: c.scope; };
    viewDefinition = f.definition;
    viewRelation = f.relation;
    target = v.placement.targets.root {
      scope = "leaf";
      channel = "settings";
    };
    unit = v.unit {
      inherit (f) relation;
      target = v.placement.targets.root {
        scope = "leaf";
        channel = "settings";
      };
      mode = "merge";
    };
  };
  functionFields = builtins.concatMap (
    k:
    let
      s = shapes.${k} genuine.${k};
    in
    map (n: "${k}.${n}") (
      builtins.filter (n: (s.${n}.what or null) == "a function") (builtins.attrNames s)
    )
  ) (builtins.attrNames shapes);

  inert = forgedRead: {
    expr = forgedRead;
    expected = genuineRead;
  };
  refused = expr: msg: {
    expr = builtins.deepSeq expr true;
    expectedError = {
      type = "ThrownError";
      inherit msg;
    };
  };
  # a forged L: the genuine alphabet with `extra` letters appended and `member` replaced
  forgedL =
    extra:
    f.labels
    // {
      letters = f.labels.letters ++ extra;
      member = forty2;
    };
  layersWith =
    extra:
    [
      [ "include" ]
      [ "parent" ]
    ]
    ++ map (l: [ l ]) extra;
  orderWith =
    extra:
    v.labelOrder {
      alphabet = forgedL extra;
      layers = layersWith extra;
      endOfPath = -1;
    };
  # a hand-built carrier over a forged L, reaching `scopeGraph` without passing `carrier`
  carrierForgedL =
    extra:
    f.carrier
    // {
      labels = forgedL extra;
      labelWellFormedness = f.admission // {
        alphabet = forgedL extra;
      };
      labelOrder = f.order // {
        alphabet = forgedL extra;
      };
    };
in
{
  flake.testsError.forged-result = {
    test-every-function-field-of-every-shape-has-a-disposition = {
      expr = {
        fields = builtins.sort builtins.lessThan functionFields;
        unsampled = builtins.filter (k: !(genuine ? ${k})) (builtins.attrNames shapes);
      };
      expected = {
        fields = builtins.sort builtins.lessThan (builtins.attrNames disposition);
        unsampled = [ ];
      };
    };

    # restated — edgeLabels.member, at every construct that tests L-membership
    test-a-forged-letters-member-is-inert-through-admission-order-carrier-and-graph = inert (
      relOverLabels badLabels
    );
    test-a-forged-letters-member-is-inert-at-labelWellFormedness = {
      expr = (admissionOver badLabels).literals;
      expected = f.admission.literals;
    };
    test-a-forged-letters-member-is-inert-at-labelOrder = {
      expr = (orderOver badLabels).layers;
      expected = f.order.layers;
    };
    # restated — relations.member / relatumLabels.member
    test-a-forged-relations-member-is-inert-at-the-carrier-graph-and-lookup = inert (
      viaGraph (graphOver (v.carrier (carrierArgs // { relations = badRels; })) { })
    );
    test-a-forged-relations-member-is-inert-at-relationEntries = {
      expr = v.relationEntries {
        graph = f.graph // {
          carrier = f.carrier // {
            relations = badRels;
          };
        };
        scope = "root";
        relation = "import";
        wellFormed = f.admitAll;
      };
      expected = v.relationEntries {
        graph = f.graph;
        scope = "root";
        relation = "import";
        wellFormed = f.admitAll;
      };
    };
    test-a-forged-relatum-member-is-inert-on-a-graph-with-a-relatum-edge = inert (
      viaGraph (graphOver (v.carrier (carrierArgs // { relatumLabels = badRoles; })) roleEdge)
    );
    # restated — the walk's derivative and its state key
    test-a-forged-step-returning-an-int-is-inert = inert (viaDef {
      admission = f.admission // {
        step = _: forty2;
      };
    });
    test-a-forged-step-returning-a-malformed-state-is-inert = inert (viaDef {
      admission = f.admission // {
        step = _: _: { t = "lit"; };
      };
    });
    test-a-forged-stateKey-returning-a-lambda-is-inert = inert (viaDef {
      admission = f.admission // {
        stateKey = _: (x: x);
      };
    });
    test-a-forged-stateKey-returning-an-int-is-inert = inert (viaDef {
      admission = f.admission // {
        stateKey = forty2;
      };
    });

    # refused-list — the lists the restatement reads meet their constructor's law at intake
    test-a-forged-letters-carrying-the-end-marker-is-refused-at-labelOrder =
      refused (orderWith [ "$" ]).rankOf
        "^gen-view\\.labelOrder: field 'alphabet\\.letters' carries the reserved letter '\\$' .*$";
    test-a-forged-letters-carrying-the-wildcard-is-refused-at-labelOrder =
      refused (orderWith [ "_" ]).rankOf
        "^gen-view\\.labelOrder: field 'alphabet\\.letters' carries the reserved letter '_' .*$";
    test-a-forged-letters-carrying-a-metacharacter-is-refused-at-labelOrder =
      refused (orderWith [ "a|b" ]).rankOf
        "^gen-view\\.labelOrder: field 'alphabet\\.letters' carries the letter 'a\\|b', which is outside the label word alphabet.*$";
    test-a-forged-letters-carrying-the-end-marker-is-refused-at-scopeGraph =
      refused
        (v.scopeGraph {
          carrier = carrierForgedL [ "$" ];
          inherit (f) scopes;
          edges = f.edges // {
            "$" = id: if id == "root" then [ "leaf" ] else [ ];
          };
          data = f.authored f.datums;
        }).labeled
        "^gen-view\\.scopeGraph: field 'carrier\\.labelOrder\\.alphabet\\.letters' carries the reserved letter '\\$' .*$";
    # The refusal names the ONE field path that carries the letter, so a door reaching L by several
    # paths says which declaration to fix: here only the admission's alphabet is forged.
    test-a-forged-letters-refusal-names-the-field-that-carries-it =
      refused
        (v.scopeGraph {
          carrier = f.carrier // {
            labelWellFormedness = f.admission // {
              alphabet = forgedL [ "$" ];
            };
          };
          inherit (f) scopes edges;
          data = f.authored f.datums;
        }).labeled
        "^gen-view\\.scopeGraph: field 'carrier\\.labelWellFormedness\\.alphabet\\.letters' carries the reserved letter '\\$' .*$";
    test-a-forged-empty-relations-is-refused-at-the-carrier = refused (v.carrier (
      carrierArgs
      // {
        relations = f.relations // {
          names = [ ];
        };
      }
    )) "^gen-view\\.carrier: field 'relations\\.names' is empty;.*$";
    test-a-forged-member-cannot-hide-a-collision-the-letters-state =
      let
        L = forgedL [ "import" ];
      in
      refused (v.carrier (
        carrierArgs
        // {
          labels = L;
          labelWellFormedness = admissionOver L;
          labelOrder = v.labelOrder {
            alphabet = L;
            layers = layersWith [ "import" ];
            endOfPath = -1;
          };
        }
      )) "^gen-view\\.carrier: 'import' is both a letter of L and a name in R;.*$";

    # unapplied — a forged result changes nothing the library answers
    test-forged-unapplied-functions-are-inert = inert (viaDef {
      admission = f.admission // {
        accepts = forty2;
      };
      order = f.order // {
        precedes = _: forty2;
        rankWord = forty2;
        pathPrecedes = _: forty2;
        rankLess = _: forty2;
      };
    });
  };
}
