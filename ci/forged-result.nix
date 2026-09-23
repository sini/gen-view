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
    "labelOrder.rankOf" = "restated";
    "dataOrder.keyOf" = "checked";
    "viewDefinition.wellFormed" = "checked";
    "viewDefinition.distance" = "checked";
    "labelWellFormedness.accepts" = "unapplied";
    "labelOrder.precedes" = "unapplied";
    "labelOrder.rankWord" = "unapplied";
    "labelOrder.pathPrecedes" = "unapplied";
    "labelOrder.rankLess" = "unapplied";
    "combine.op" = "restated";
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
  # A function NESTED inside a non-function, non-element field (den-hoag-cer8j): the top-level census
  # above reads the shape register, which types such a field `set`/`list`/`any` and cannot see in.
  # This walks the genuine VALUES; a field whose value holds a function leaf needs a disposition.
  nestedDisposition = {
    "scopeGraph.labeled" = "restated";
    "scopeGraph.edges" = "checked";
  };
  holdsFunction =
    d: x:
    builtins.isFunction x
    || (
      d > 0
      && !(builtins.isAttrs x && x ? __element)
      && (
        (builtins.isAttrs x && builtins.any (n: holdsFunction (d - 1) x.${n}) (builtins.attrNames x))
        || (builtins.isList x && builtins.any (holdsFunction (d - 1)) x)
      )
    );
  nestedFields = builtins.concatMap (
    k:
    let
      s = shapes.${k} genuine.${k};
    in
    map (n: "${k}.${n}") (
      builtins.filter (
        n: !(s.${n} ? element) && (s.${n}.what or null) != "a function" && holdsFunction 5 genuine.${k}.${n}
      ) (builtins.attrNames s)
    )
  ) (builtins.attrNames shapes);
  forgedLabeled = over: f.graph // { labeled = f.graph.labeled // over; };
  # A derived VALUE is a claim too (den-hoag-dcvpi): every non-function, non-element field of every
  # shape is classified, and the census cell holds the classification equal to the register.
  #
  #   restated  the library derives the value from checked structure and never reads the field
  #   checked   read, and held to its constructor's law where it is read (at intake or the door)
  #   declared  the caller's own argument, stored as given; nothing derives it
  #   unread    derived, published, and read by nothing in the library
  valueDisposition = {
    "combine.acc" = "declared";
    "combine.arm" = "declared";
    "combine.associative" = "restated";
    "combine.setSemilattice" = "restated";
    "combine.unit" = "restated";
    "dataOrder.channel" = "declared";
    "dedup.arm" = "declared";
    "edgeLabels.extended" = "restated";
    "edgeLabels.letters" = "checked";
    "labelOrder.endOfPath" = "checked";
    "labelOrder.layers" = "checked";
    "labelWellFormedness.expr" = "restated";
    "labelWellFormedness.expression" = "checked";
    "labelWellFormedness.literals" = "unread";
    "relations.names" = "checked";
    "relatumLabels.names" = "checked";
    "scopeGraph.data" = "checked";
    "scopeGraph.datumsAt" = "restated";
    "scopeGraph.edges" = "checked";
    "scopeGraph.labeled" = "restated";
    "scopeGraph.scopes" = "checked";
    "target.arm" = "declared";
    "target.channel" = "declared";
    "target.scope" = "declared";
    "tieSet.arm" = "declared";
    "tieSet.order" = "declared";
    "unit.mode" = "declared";
    "viewDefinition.direction" = "declared";
    "viewDefinition.empty" = "declared";
    "viewDefinition.name" = "restated";
    "viewDefinition.relation" = "declared";
    "viewDefinition.root" = "declared";
    "viewRelation.name" = "restated";
  };
  valueFields = builtins.concatMap (
    k:
    let
      s = shapes.${k} genuine.${k};
    in
    map (n: "${k}.${n}") (
      builtins.filter (n: !(s.${n} ? element) && (s.${n}.what or null) != "a function") (
        builtins.attrNames s
      )
    )
  ) (builtins.attrNames shapes);
  forgedDatumsAt = over: f.graph // { datumsAt = over; };
  entriesAt =
    g: scope:
    v.relationEntries {
      graph = g;
      inherit scope;
      relation = "import";
      wellFormed = _: true;
    };
  rootTo =
    channel:
    v.placement.targets.root {
      scope = "leaf";
      inherit channel;
    };
  inboundDef = f.mkDefinition {
    direction = "inbound";
    root = "root";
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
    # restated — scopeGraph.labeled, from the checked edges, scopes and carrier (den-hoag-cer8j)
    test-every-function-nested-in-an-element-field-has-a-disposition = {
      expr = builtins.sort builtins.lessThan nestedFields;
      expected = builtins.sort builtins.lessThan (builtins.attrNames nestedDisposition);
    };
    test-a-forged-labeled-answering-no-edges-is-inert = inert (
      viaGraph (forgedLabeled {
        labeledEdges = _: [ ];
      })
    );
    test-a-forged-labeled-adding-an-edge-is-inert = inert (
      viaGraph (forgedLabeled {
        labeledEdges =
          id:
          f.graph.labeled.labeledEdges id
          ++ [
            {
              label = "parent";
              target = "root";
            }
          ];
      })
    );
    test-a-forged-labeled-returning-an-int-is-inert = inert (
      viaGraph (forgedLabeled {
        labeledEdges = forty2;
      })
    );
    test-a-forged-labeled-with-no-labeledEdges-is-inert = inert (
      viaGraph (f.graph // { labeled = { inherit (f.graph) scopes; }; })
    );
    test-a-forged-labeled-is-inert-on-an-inbound-walk = {
      expr = read (
        f.mkRelation {
          definition = inboundDef;
          graph = forgedLabeled { labeledEdges = _: [ ]; };
        }
      );
      expected = read (f.mkRelation { definition = inboundDef; });
    };
    # what the restatement reads meets the constructor's law at the reading door
    test-forged-edges-with-a-non-accessor-are-refused-at-viewRelation = refused (viaGraph (
      f.graph
      // {
        edges = f.edges // {
          include = 42;
        };
      }
    )) "^gen-view\\.viewRelation: field 'graph\\.edges' carry the label 'include' bound to 42;.*$";
    test-forged-edges-with-an-unclassified-label-are-refused-at-viewRelation =
      refused
        (viaGraph (
          f.graph
          // {
            edges = f.edges // {
              bogus = _: [ ];
            };
          }
        ))
        "^gen-view\\.viewRelation: field 'graph\\.edges' carry the label 'bogus', which is in none of the three populations.*$";
    test-forged-scopes-carrying-a-non-string-are-refused-at-viewRelation = refused (viaGraph (
      f.graph // { scopes = f.scopes ++ [ 1 ]; }
    )) "^gen-view\\.viewRelation: field 'graph\\.scopes' carries a int where a string is required.*$";
    test-forged-edges-with-an-off-scope-target-are-refused-by-name =
      refused
        (viaGraph (
          f.graph
          // {
            edges = f.edges // {
              include = _: [ "nowhere" ];
            };
          }
        ))
        "^gen-view\\.scopeGraph: the edge accessor 'include' at scope 'leaf' returned the target \"nowhere\", which is not a scope of this graph.*$";
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
    # restated — derived VALUES, from checked structure (den-hoag-dcvpi)
    test-every-value-field-of-every-shape-has-a-disposition = {
      expr = builtins.sort builtins.lessThan valueFields;
      expected = builtins.sort builtins.lessThan (builtins.attrNames valueDisposition);
    };
    test-a-forged-datumsAt-answering-nothing-is-inert = inert (viaGraph (forgedDatumsAt { }));
    test-a-forged-datumsAt-replacing-a-datum-is-inert = inert (
      viaGraph (
        forgedDatumsAt (
          f.graph.datumsAt
          // {
            root = [
              {
                scope = "root";
                relation = "import";
                datum = [ "forged" ];
                ordinal = 0;
              }
            ];
          }
        )
      )
    );
    test-a-forged-datumsAt-is-inert-at-relationEntries = {
      expr = entriesAt (forgedDatumsAt { }) "inc";
      expected = entriesAt f.graph "inc";
    };
    test-forged-data-off-scope-is-refused-at-relationEntries =
      refused
        (viaGraph (
          f.graph
          // {
            data = f.graph.data ++ [
              {
                scope = "nowhere";
                relation = "import";
                datum = 1;
              }
            ];
          }
        ))
        "^gen-view\\.relationEntries: a datum of field 'graph\\.data' is filed at scope 'nowhere', which is not a scope of this graph.*$";
    test-forged-data-carrying-a-walk-field-is-refused-at-relationEntries =
      refused
        (viaGraph (
          f.graph
          // {
            data = f.graph.data ++ [
              {
                scope = "root";
                relation = "import";
                datum = 1;
                path = [ ];
              }
            ];
          }
        ))
        "^gen-view\\.relationEntries: a datum of field 'graph\\.data' carries the fields \\(datum, path, relation, scope\\);.*$";
    test-a-forged-expr-is-inert = inert (viaDef {
      admission = f.admission // {
        expr =
          (v.labelWellFormedness {
            alphabet = f.labels;
            expression = "parent*";
          }).expr;
      };
    });
    test-a-forged-extended-is-inert = inert (viaDef {
      order = f.order // {
        alphabet = f.labels // {
          extended = f.labels.letters;
        };
      };
    });
    test-a-forged-definition-name-is-inert = inert (viaDef {
      name = "other";
    });
    test-a-forged-relation-name-is-refused-where-the-genuine-one-is =
      refused
        (v.writesOf {
          relation = f.relation // {
            name = "other";
          };
          target = rootTo "other";
          mode = "merge";
        })
        "^gen-view\\.writesOf: the target names channel 'other' but the view relation is named 'settings';.*$";

    # restated — combine's arm-decided fields and labelOrder's rankOf (den-hoag-6vsvx)
    test-a-forged-combine-op-is-inert = inert (viaDef {
      combine = f.definition.combine // {
        op = _: _: [ "forged" ];
      };
    });
    # The lawful-looking forgery: an associative op of the arm's type with its operands swapped.
    # One contribution cannot show it, so it folds `flatOrder`'s two ([ "inc" "mid" ]).
    test-a-forged-operand-swap-is-inert =
      let
        flatUnder =
          combine:
          read (
            f.mkRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                inherit combine;
              };
            }
          );
      in
      {
        expr = flatUnder (v.combines.listAppend // { op = a: b: b ++ a; });
        expected = flatUnder v.combines.listAppend;
      };
    test-a-forged-combine-unit-is-inert = inert (viaDef {
      combine = f.definition.combine // {
        unit = [ "forged" ];
      };
    });
    test-a-forged-combine-associative-is-inert = inert (viaDef {
      combine = f.definition.combine // {
        associative = false;
      };
    });
    test-a-seed-matching-a-forged-unit-is-refused-by-name =
      refused
        (viaDef {
          combine = f.definition.combine // {
            unit = [ "forged" ];
          };
          empty = [ "forged" ];
        })
        "^gen-view\\.viewRelation: field 'definition\\.empty' is \\[\"forged\"\\], which is not the unit of the declared combine arm \"listAppend\";.*$";
    test-a-forged-setSemilattice-cannot-drop-the-acc-flag =
      refused
        (f.mkDefinition {
          combine = v.combines.setUnion { acc = true; } // {
            setSemilattice = false;
            acc = null;
          };
        })
        "^gen-view\\.viewDefinition: field 'combine' names the set-semilattice arm 'setUnion' with no declared ACC flag;.*$";
    test-a-forged-rankOf-is-inert = inert (viaDef {
      order = f.order // {
        rankOf =
          l:
          if l == "parent" then
            0
          else if l == "include" then
            1
          else
            -1;
      };
    });
    test-a-forged-order-mark-rankOf-is-inert = inert (
      read (
        f.mkRelation {
          orderMark = f.identityMark // {
            rankOf =
              l:
              if l == "parent" then
                0
              else if l == "include" then
                1
              else
                -1;
          };
        }
      )
    );
    test-forged-layers-are-refused-by-name-at-viewRelation =
      refused
        (viaDef {
          order = f.order // {
            layers = [
              [ "include" ]
              [ "parent" ]
              [ "nope" ]
            ];
          };
        })
        "^gen-view\\.viewRelation: field 'definition\\.order\\.layers' rank 'nope', which is not a letter of the alphabet.*$";

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
