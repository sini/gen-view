# THE SECOND TEST OUTPUT — cells whose subject is an ERROR MESSAGE, and the runner that reads them.
#
# ★★ WHY A SECOND OUTPUT RATHER THAN A SECOND SUITE. `mkCi` builds `checks.default` from an
# asserter that evaluates `t.expr == t.expected` UNCONDITIONALLY and quantifies over
# `config.flake.tests`. A cell with no `expected` and a throwing `expr` therefore CRASHES that
# batch gate rather than failing it. Hosting these on `flake.testsError` puts them outside the
# asserter's quantifier while keeping them live on the nix-unit path.
#
# ★★ AND THE SPLIT IS STRUCTURAL, NOT CONVENTIONAL. This file is NOT under `./tests`, which is the
# whole of `testModules`, so nothing about which cells land in which output depends on a filter
# predicate or an ignore convention a dependency bump could redefine. It reaches the flake through
# `mkCi`'s `extraModules`.
#
# ★★★ THIS OUTPUT IS THE HALF OF ORACLE O1 THAT MAKES A REFUSAL *NAMED*. `ci/tests/refusals.nix`
# asserts that a refusal HAPPENED — a boolean, which `tryEval` can carry. WHICH FIELD it named is a
# claim about the message, and `expectedError` is the only assertion available for that. A suite
# with only the boolean half would go green on a library that refused every omission with one
# undifferentiated message, which is precisely the failure O1 lists: "any refusal is UNNAMED".
#
#   nix-unit --flake ./ci#tests        # the suite
#   nix-unit --flake ./ci#testsError   # these cells
{
  genView,
  genScope,
  ...
}:
let
  f = import ./fixture.nix { inherit genView; };
  r = import ./reference-fixture.nix { inherit genView genScope; };
  v = genView;
in
{
  config = {
    # ── EVERY OMITTED FIELD IS NAMED, ONE CELL PER FIELD ──
    # Generated from the library's own field enumeration, so a thirteenth field cannot arrive
    # without a message cell arriving with it. The pattern is anchored at the front and pins the
    # FIELD NAME, which is the whole content of the claim.
    flake.testsError.named-refusals =
      builtins.listToAttrs (
        map (field: {
          name = "test-omitting-${field}-names-the-field";
          value = {
            expr = builtins.deepSeq (v.viewDefinition (removeAttrs f.definitionArgs [ field ])) true;
            expectedError = {
              type = "ThrownError";
              msg = "^gen-view\\.viewDefinition: required field '${field}' is not declared; every field of this construct is required and total .*$";
            };
          };
        }) v.definitionFields
      )
      // {
        # ★ THE LIVE CONTROL, IN THE SAME INVOCATION. Without it every cell above is consistent
        # with a construct that refuses whatever it is handed, and the messages would be about a
        # constructor nobody has seen succeed. It is an `expected` cell in an `expectedError`
        # output on purpose: a control has to run in the same run as the thing it controls.
        test-control-the-complete-definition-does-not-refuse = {
          expr = (v.viewDefinition f.definitionArgs).name;
          expected = "settings";
        };

        # A FIELD NOBODY DECLARED is named too — the other half of totality, and the arm that makes
        # widening unsayable at the materialization.
        test-an-undeclared-field-is-named = {
          expr = builtins.deepSeq (v.viewRelation {
            definition = f.definition;
            graph = f.graph;
            marks = f.noMarks;
            widen = _: true;
          }) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: field 'widen' is not a field of this construct; the field set is closed .*$";
          };
        };
      };

    # ── REFERENCE RESOLUTION: EVERY OMITTED FIELD IS NAMED, ONE CELL PER FIELD ──
    # Generated from the construct's own field enumeration, so an eighth field cannot arrive
    # without a message cell arriving with it. What makes these cells worth their length is the
    # thing they replace: the wrapper this construct succeeds left FOUR of these seven to silent
    # defaults, and a default is a decision nobody made and nobody can see.
    flake.testsError.reference-refusals =
      builtins.listToAttrs (
        map (field: {
          name = "test-omitting-reference-${field}-names-the-field";
          value = {
            expr = builtins.deepSeq (v.referenceResolution (removeAttrs r.referenceArgs [ field ])) true;
            expectedError = {
              type = "ThrownError";
              msg = "^gen-view\\.referenceResolution: required field '${field}' is not declared; every field of this construct is required and total .*$";
            };
          };
        }) v.referenceResolutionFields
      )
      // {
        # ★ THE LIVE CONTROL, IN THE SAME INVOCATION. Without it every cell above is consistent
        # with a construct that refuses whatever it is handed, and the messages would be about a
        # constructor nobody has seen succeed.
        test-control-the-complete-reference-declaration-does-not-refuse = {
          expr = (v.referenceResolution r.referenceArgs).name;
          expected = "resolvedProvides";
        };

        # The closed field set names the offender — and the name chosen here is the one a reader is
        # most likely to try, because a `codomain` literal is exactly what this construct declines
        # to publish: the disposal is selected inside the authority's closure on a runtime type, so
        # no constructor could derive it and no constant could stay true about it.
        test-an-undeclared-reference-field-is-named = {
          expr = builtins.deepSeq (v.referenceResolution (
            r.referenceArgs // { codomain = "atMostOne"; }
          )) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.referenceResolution: field 'codomain' is not a field of this construct; the field set is closed .*$";
          };
        };

        # The injected authority, named with what it must publish — a caller who handed the wrong
        # value needs to know which surface was wanted, not that one was refused.
        test-an-engine-publishing-no-query-is-named = {
          expr = builtins.deepSeq (v.referenceResolution (r.referenceArgs // { engine = { }; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.referenceResolution: field 'engine' must be a query authority publishing a 'query'.*performs no resolution of its own.*$";
          };
        };

        # The two operators are named as operators, because a caller who fused them needs to meet
        # the reason and not the type complaint: a predicate that also projects cannot be split
        # into π and σ, which is why the split is not a matter of taste.
        test-a-non-function-projection-is-named-as-an-operator = {
          expr = builtins.deepSeq (v.referenceResolution (r.referenceArgs // { project = [ ]; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.referenceResolution: field 'project' must be a function.*a predicate that also projects cannot be split into the two operators.*$";
          };
        };

        # ★ THE FLAG IS NAMED INDIVIDUALLY, which is the whole reason the three are checked through
        # a list rather than by one `all` over them. A message saying "a flag is not a boolean"
        # would leave the caller to find out which.
        test-a-non-boolean-discipline-flag-names-which-one = {
          expr = builtins.deepSeq (v.referenceResolution (
            r.referenceArgs // { importShadowsParent = null; }
          )) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.referenceResolution: field 'importShadowsParent' is null, which is not a boolean.*DECLARED here rather than left to the authority's defaults.*$";
          };
        };

        # ★★★ THE MATERIALIZATION REFUSAL, NAMED WITH THE RESULT AND THE NODE. This is the fused
        # predicate's third defect closed, and the message has to carry both coordinates: a caller
        # meets it while forcing some attribute far from the declaration, and "a projection was
        # null" without the result name and the node is a fact they cannot act on.
        test-a-null-projection-names-the-result-and-the-node = {
          expr = builtins.deepSeq (r.projectionSelf.get "reader" "nullArm") true;
          expectedError = {
            type = "ThrownError";
            msg = ".*gen-view\\.referenceResolution: result 'tagOfNearestHolder': node 'holder' is admitted by 'wellFormed' and its 'project' returned null.*NO BINDING HERE.*";
          };
        };

        # ★ THE CONTROL THAT SEPARATES THAT REFUSAL FROM AN ORDINARY ABSENCE, on the same fixture in
        # the same run: a node whose only candidate the predicate DECLINES answers null and does not
        # refuse. Without it, the cell above is consistent with a guard that fired on every miss.
        test-control-an-unadmitted-node-answers-null-without-refusing = {
          expr = r.projectionSelf.get "lonely" "nullArm";
          expected = null;
        };
      };

    # ── THE CARRIER'S OWN REFUSALS NAME THEIR SUBJECT ──
    flake.testsError.carrier-refusals = {
      # The letter, not merely "an unranked letter".
      test-an-unranked-letter-is-named = {
        expr = builtins.deepSeq (v.labelOrder {
          alphabet = f.labels;
          layers = [ [ "parent" ] ];
          endOfPath = -1;
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.labelOrder: letter 'include' is not ranked; the label order is total over the alphabet.*$";
        };
      };

      # The offending name AND the alphabet it is not in, because a caller who wrote a relation
      # name into a path expression needs to see both populations to see the mistake.
      test-a-relation-name-in-a-path-expression-is-named-with-the-alphabet = {
        expr = builtins.deepSeq (v.labelWellFormedness {
          alphabet = f.labels;
          expression = "import*";
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.labelWellFormedness: the expression names 'import', which is not a letter of the alphabet \\(include, parent\\).*$";
        };
      };

      # The undeclared relation and the sort it is not in. ★ THIS IS THE ONE THAT REPLACES A
      # MEASURED SILENT FAILURE: in the grammar this library succeeds, a misspelled channel yields
      # `{ }` and the undeclared-channel check reads `false` even under `deepSeq`.
      test-an-undeclared-relation-is-named-with-the-sort = {
        expr = builtins.deepSeq (v.relationLookup {
          graph = f.graph;
          scope = "inc";
          relation = "not-declared";
          wellFormed = f.admitAll;
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.relationLookup: 'not-declared' is not a name in R \\(broadcast-in, expose-in, import, policy\\).*$";
        };
      };

      # The overlapping name, at the one place that can see both sorts at once.
      test-a-name-in-both-sorts-is-named = {
        expr = builtins.deepSeq (v.carrier {
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
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.carrier: 'parent' is both a letter of L and a name in R; the sorts are disjoint.*$";
        };
      };

      # ★★★ THE Λ COLLISION IS NAMED, AND SO IS *WHY*. A role label that is also a letter would make
      # a binding's incident edge WALKABLE: the derivative would not go to the empty state, the walk
      # would step onto a relatum edge, and the inertness that keeps a binding out of the traversal
      # would be false while still being written down. The message carries that reason, because a
      # caller who hits it has a naming collision and no way to see what it costs.
      test-a-relatum-label-colliding-with-a-letter-is-named = {
        expr = builtins.deepSeq (v.carrier {
          labels = f.labels;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
          relations = f.relations;
          relatumLabels = v.relatumLabels { names = [ "parent" ]; };
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.carrier: 'parent' is both a letter of L and a relatum label in Λ; the populations are disjoint.*WALKABLE.*$";
        };
      };

      # The third pair of the three-way condition, named the same way.
      test-a-relatum-label-colliding-with-a-relation-is-named = {
        expr = builtins.deepSeq (v.carrier {
          labels = f.labels;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
          relations = f.relations;
          relatumLabels = v.relatumLabels { names = [ "import" ]; };
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.carrier: 'import' is both a name in R and a relatum label in Λ; the populations are disjoint.*$";
        };
      };

      # EXHAUSTIVENESS: a label in NONE of the three populations names all three, so the reader can
      # see which one it was meant to join.
      test-an-edge-label-in-no-population-names-all-three = {
        expr = builtins.deepSeq (v.scopeGraph {
          carrier = f.carrier;
          scopes = [ "leaf" ];
          edges = {
            not-a-population = _: [ ];
          };
          data = f.authored { };
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.scopeGraph: edges carry the label 'not-a-population', which is in none of the three populations — L \\(include, parent\\), R \\(broadcast-in, expose-in, import, policy\\) or Λ \\(relatum-source, relatum-target\\).*$";
        };
      };

      # ★★★ A FUNCTION IN THE DATA POSITION IS REFUSED WITH THE REASON, NOT MERELY WITH A TYPE
      # COMPLAINT — and the message is asserted because the VERDICT alone does not distinguish this
      # branch from the generic "must be a list" one. Measured: disabling this branch leaves every
      # boolean cell green, because the list check catches a function too. What would be lost is the
      # only place the library says WHY a function is the one shape that may not appear here — it is
      # the withdrawn divergence, the construction that made walk-dependence sayable in the first
      # place, and a reader who reintroduces it will meet this sentence or nothing.
      test-a-function-in-the-data-position-names-the-withdrawn-divergence = {
        expr = builtins.deepSeq (v.scopeGraph {
          carrier = f.carrier;
          scopes = [ "leaf" ];
          edges = { };
          data = _: _: [ ];
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.scopeGraph: data is a FUNCTION; it must be a plain list of datums.*COMPONENT of the graph.*let the substrate's own accessor re-emit.*$";
        };
      };

      # And the generic shape complaint is a DIFFERENT message, so the two are not one branch
      # wearing two descriptions.
      test-a-non-list-data-component-names-the-shape = {
        expr = builtins.deepSeq (v.scopeGraph {
          carrier = f.carrier;
          scopes = [ "leaf" ];
          edges = { };
          data = "not a list";
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.scopeGraph: data must be a list of datums.*Fig\\. 1's `Data ::= s —r→ d`.*$";
        };
      };

      # ★★ A CONTRIBUTION IN A DATA POSITION IS NAMED WITH ITS EXTRA FIELDS, so the reader sees
      # exactly why a walk answer is not a datum and what authoring one would mean.
      test-a-contribution-in-a-data-position-names-its-fields = {
        expr = builtins.deepSeq (v.scopeGraph {
          carrier = f.carrier;
          scopes = f.scopes;
          edges = f.edges;
          data = [ (builtins.head f.relation.contributions) ];
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.scopeGraph: a datum carries the fields \\(admission, channel, datum, distance, path, relation, scope\\); a datum is exactly .* A WALK ANSWER CANNOT BE A DATUM.*$";
        };
      };

      # LIVE CONTROL: the carrier that meets all three conditions constructs and carries its five.
      test-control-a-well-formed-carrier-constructs = {
        expr = f.carrier.__element;
        expected = "carrier";
      };
    };

    # ── THE MATERIALIZATION'S REFUSALS NAME THE CHANNEL AND THE CAUSE ──
    flake.testsError.materialization-refusals = {
      # `refuse` names the channel, the count and the contributing scopes — the material a caller
      # needs to resolve the tie, not the verdict that one exists.
      test-a-refused-tie-names-the-channel-and-the-tied-scopes = {
        expr =
          builtins.deepSeq
            (f.mkRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                tieSet = v.tieSets.refuse;
              };
            }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.viewRelation: channel 'settings' declares tieSet 'refuse' and the competition key \"settings\" survives with 2 contributions, from scopes inc, mid.*$";
        };
      };

      # An `orderedFold` whose declared order does not rank a surviving scope names THAT scope: the
      # order is total over the surviving set, and a scope it does not name would otherwise sort to
      # an end nobody declared.
      test-an-unranked-surviving-scope-is-named = {
        expr =
          builtins.deepSeq
            (f.mkRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                tieSet = v.tieSets.orderedFold { order = [ "mid" ]; };
              };
            }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.viewRelation: channel 'settings' declares tieSet 'orderedFold' whose declared order \\(mid\\) does not rank the contributing scope 'inc'.*$";
        };
      };

      # ★ THE LIVE CONTROL FOR BOTH: the SAME fixture under `union` materializes. The two cells
      # above pass by refusing, so without a counterpart they would go green on a fixture that
      # cannot be materialized at all.
      test-control-the-same-fixture-under-union-materializes = {
        expr = (f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }).value;
        expected = [
          "inc"
          "mid"
        ];
      };

      # The ordering door names the raw labelled-edge accessor specifically, so the reader meets
      # the REASON and not just the denial: the input type is the stratification.
      test-the-ordering-door-names-the-raw-accessor = {
        expr = builtins.deepSeq (v.readsOf f.graph.labeled) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.readsOf: field 'relation' is a RAW LABELLED-EDGE ACCESSOR; this door takes the materialized result and only that.*$";
        };
      };

      # ★★★ THE MATERIALIZATION NAMES THE UNDECLARED RELATION AND THE SORT, through the PUBLISHED
      # lookup rather than through a second refusal path. Before the fix this call answered `[ ]`
      # and said nothing, indistinguishable from a declared relation with no datums — the failure
      # `lib/refusal.nix` names as the precedent it exists to forbid, reproduced by the library
      # against itself. The message is `relationLookup`'s own, which is the point: there is one
      # refusal here, not two to keep in step.
      test-the-materialization-names-an-undeclared-relation = {
        expr =
          builtins.deepSeq
            (f.mkRelation { definition = f.mkDefinition { relation = "not-a-relation"; }; }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.relationLookup: 'not-a-relation' is not a name in R \\(broadcast-in, expose-in, import, policy\\); an undeclared relation is refused rather than answered empty.*$";
        };
      };

      # ★ THE CONTROL THAT SEPARATES A REFUSAL FROM AN EMPTY ANSWER, on the SAME path in the SAME
      # run: a DECLARED relation with no datums anywhere materializes to the empty value and does
      # not refuse. Without it the cell above is consistent with a materialization that refuses
      # whenever its gather comes back empty.
      test-control-a-declared-relation-with-no-datums-materializes-empty = {
        expr = (f.mkRelation { definition = f.mkDefinition { relation = "expose-in"; }; }).value;
        expected = [ ];
      };

      # LIVE CONTROL: the door accepts the materialized projection.
      test-control-the-ordering-door-accepts-the-materialized-projection = {
        expr = v.readsOf f.relation;
        expected = [ "inc/settings@input" ];
      };
    };
  };
}
