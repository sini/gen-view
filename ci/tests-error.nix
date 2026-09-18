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
  graph,
  ...
}:
let
  f = import ./fixture.nix { inherit genView; };
  r = import ./reference-fixture.nix { inherit genView genScope; };
  v = genView;

  # ══ W1 FIXTURE — boundedWellDefinedSchedule, ORACLE O2 and O5a ══
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
  # `child` alone is a SOURCE in the index; `parent` (a sink only) is absent from its keys — the
  # fixture C-1's third arm needs to show `nodes = attrNames index` silently omitting a sink.
  wdsDeclaredAcyclic = wdsContracted { child = [ "parent" ]; };
  wdsScheduleArgs = {
    nodes = [
      "child"
      "parent"
    ];
    equations = { };
    declaredDependencies = wdsDeclaredCyclic;
    admitsCycle = _: false;
  };
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
            orderMark = f.identityMark;
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
        # to publish: A REFUSAL IS NOT A CARDINALITY. The authority answers with one declaration or
        # throws, and the refusal fires inside its closure over a candidate set that does not exist
        # until the query runs, so no constructor could derive it and no constant could stay true
        # about it.
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

    # ── `neededBy`: EVERY OMITTED FIELD IS NAMED, ONE CELL PER FIELD ──
    # Generated from the REVERSE construct's own field enumeration — a third generator rather than a
    # widened one, because the two constructs share four field names and differ in the fifth, and a
    # sweep quantified over the wrong enumeration would look complete while omitting exactly the
    # field that distinguishes them.
    flake.testsError.neededby-refusals =
      builtins.listToAttrs (
        map (field: {
          name = "test-omitting-neededby-${field}-names-the-field";
          value = {
            expr = builtins.deepSeq (v.neededBy (removeAttrs r.reverseArgs [ field ])) true;
            expectedError = {
              type = "ThrownError";
              msg = "^gen-view\\.neededBy: required field '${field}' is not declared; every field of this construct is required and total .*$";
            };
          };
        }) v.neededByFields
      )
      // {
        # ★ THE LIVE CONTROL, IN THE SAME INVOCATION, for the reason both sweeps above carry one:
        # without it every cell here is consistent with a construct that refuses whatever it is
        # handed, and the messages would be about a constructor nobody has seen succeed.
        test-control-the-complete-neededby-declaration-does-not-refuse = {
          expr = (v.neededBy r.reverseArgs).name;
          expected = "consumers";
        };

        # ★ THE CLOSED FIELD SET NAMES THE OFFENDER, and the name chosen is the one a reader is most
        # likely to try: `transitiveImports` is the FORWARD construct's spelling of the closure flag,
        # so a caller reaching for symmetry between two constructs in one file writes it here. The
        # delegate's reverse operator owns the name `transitive` and refuses the forward spelling in
        # a way `tryEval` cannot catch, so catching it at the declaration is what keeps the failure
        # somewhere a caller can act on.
        test-the-forward-spelling-of-the-closure-flag-is-named = {
          expr = builtins.deepSeq (v.neededBy (r.reverseArgs // { transitiveImports = false; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.neededBy: field 'transitiveImports' is not a field of this construct; the field set is closed .*$";
          };
        };

        # ★★★ THE ENGINE CHECK NAMES `queryReverse` AND NOT `query`, AND THIS IS THE CELL THAT PINS
        # IT. An authority publishing only the forward operator cannot answer this construct at all,
        # so an engine check COPIED from the forward sibling would accept it here and defer the
        # failure to some later force, where it arrives as an unnamed missing-attribute error inside
        # an evaluator. Two arms: a value publishing NOTHING, and — the arm that catches the copy —
        # a value publishing exactly `query`.
        test-an-engine-publishing-no-queryreverse-is-named-with-the-operator-it-lacks = {
          expr = builtins.deepSeq (v.neededBy (r.reverseArgs // { engine = { }; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.neededBy: field 'engine' must be a query authority publishing a 'queryReverse'.*performs no traversal of its own.*$";
          };
        };

        test-a-forward-only-authority-is-named-with-the-operator-it-lacks = {
          expr = builtins.deepSeq (v.neededBy (r.reverseArgs // { engine = r.stubEngine; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.neededBy: field 'engine' must be a query authority publishing a 'queryReverse'.*only the forward 'query' cannot answer the reverse direction.*$";
          };
        };

        # The two operators are named AS OPERATORS here too — a caller who fused them meets the
        # reason and not the type complaint.
        test-a-non-function-reverse-projection-is-named-as-an-operator = {
          expr = builtins.deepSeq (v.neededBy (r.reverseArgs // { project = [ ]; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.neededBy: field 'project' must be a function.*a predicate that also projects cannot be split into the two operators.*$";
          };
        };

        # ★ THE CLOSURE FLAG IS NAMED WITH ITS VALUE. There is one such flag rather than the forward
        # half's three, so the message names it directly — and it says the closure is DECLARED here,
        # which is the whole content of the field: the wrapper this construct succeeds passed it
        # never and let the delegate's own default decide the reverse-import closure.
        test-a-non-boolean-transitive-names-the-field-and-its-value = {
          expr = builtins.deepSeq (v.neededBy (r.reverseArgs // { transitive = 0; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.neededBy: field 'transitive' is 0, which is not a boolean; the reverse-import closure is DECLARED here rather than left to the authority's default.*$";
          };
        };

        # ★★★ THE MATERIALIZATION REFUSAL, NAMED WITH THE RESULT AND THE NODE — the same guard as
        # the forward half's, reached through the other operator, which is why the message reads
        # `neededBy` here and `referenceResolution` there off ONE lifted helper. The node name is
        # what the reverse arm buys: `nodeLabel` finds a string `id` on every reverse contributor,
        # so the refusal points at the importer rather than falling to its no-`id` fallback.
        test-a-null-reverse-projection-names-the-result-and-the-importer = {
          expr = builtins.deepSeq (r.reverseNullSelf.get "db1" "gathered") true;
          expectedError = {
            type = "ThrownError";
            msg = ".*gen-view\\.neededBy: result 'consumers': node 'nullnode' is admitted by 'wellFormed' and its 'project' returned null.*NO BINDING HERE.*";
          };
        };

        # ★ THE CONTROL THAT SEPARATES THAT REFUSAL FROM AN ORDINARY ABSENCE, same fixture same run:
        # a node nothing imports gathers empty and does not refuse. An empty gather is this
        # construct's ORDINARY case, so without this row the cell above is consistent with a guard
        # that fired on every miss.
        test-control-an-empty-reverse-gather-answers-empty-without-refusing = {
          expr = r.reverseNullSelf.get "web1" "gathered";
          expected = [ ];
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
          msg = "^gen-view\\.relationEntries: 'not-declared' is not a name in R \\(broadcast-in, expose-in, import, policy\\).*$";
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
          msg = "^gen-view\\.scopeGraph: a datum carries the fields \\(admission, channel, datum, distance, element, path, relation, scope\\); a datum is exactly .* A WALK ANSWER CANNOT BE A DATUM.*$";
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
      # `relationEntries` rather than through a second refusal path. Before the fix this call
      # answered `[ ]` and said nothing, indistinguishable from a declared relation with no datums
      # — the failure `lib/refusal.nix` names as the precedent it exists to forbid, reproduced by
      # the library against itself. The message is `relationEntries`'s own, which is the point:
      # there is one refusal here, not two to keep in step.
      test-the-materialization-names-an-undeclared-relation = {
        expr =
          builtins.deepSeq
            (f.mkRelation { definition = f.mkDefinition { relation = "not-a-relation"; }; }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.relationEntries: 'not-a-relation' is not a name in R \\(broadcast-in, expose-in, import, policy\\); an undeclared relation is refused rather than answered empty.*$";
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

    # ── AUTHORSHIP-VISIBILITY (den-hoag-2vzn) — §3's O1b AND O2c NAME THE REFUSAL BY MESSAGE ──
    # `ci/tests/relation.nix` asserts these refusals as booleans (`tryEval` cannot carry a message);
    # this suite is the half that pins WHICH refusal fired, on the same construction. Built locally
    # rather than importing `ci/tests/relation.nix`'s bindings: this file's fixtures are
    # self-contained by the same convention every suite above follows.
    flake.testsError.authorship-visibility-refusals =
      let
        # §1.2's diamond alphabet — ASYMMETRIC so the two arrivals keep distinguishable admission
        # states; `ci/fixture.nix`'s own `f.admission` is symmetric and would merge them (O0's
        # masker #1). Never a custom label order: `f.flatOrder` below is the one O0 requires.
        diamondAdmission = v.labelWellFormedness {
          alphabet = f.labels;
          expression = "parent(include)*|include(parent)*";
        };

        # O1b's subject — §1.2's diamond, `leaf →p a →i top` and `leaf →i b →p top`.
        diamondScopes = [
          "leaf"
          "a"
          "b"
          "top"
        ];
        diamondEdges = {
          parent =
            id:
            {
              leaf = [ "a" ];
              b = [ "top" ];
            }
            .${id} or [ ];
          include =
            id:
            {
              leaf = [ "b" ];
              a = [ "top" ];
            }
            .${id} or [ ];
        };
        diamondData = [
          {
            scope = "top";
            relation = "import";
            datum = [ "X" ];
          }
        ];
        diamondGraph = v.scopeGraph {
          carrier = f.carrier;
          scopes = diamondScopes;
          edges = diamondEdges;
          data = diamondData;
        };

        # O2c's Z/Y — Z has no diamond (`top` and `rival` each reached once, by the SAME route
        # shape); Y is Z plus one more route to `top` alone.
        zScopes = [
          "leaf"
          "a"
          "top"
          "rival"
        ];
        zEdges = {
          parent = id: { leaf = [ "a" ]; }.${id} or [ ];
          include =
            id:
            {
              a = [
                "top"
                "rival"
              ];
            }
            .${id} or [ ];
        };
        zData = [
          {
            scope = "top";
            relation = "import";
            datum = [ "X" ];
          }
          {
            scope = "rival";
            relation = "import";
            datum = [ "R" ];
          }
        ];
        zGraph = v.scopeGraph {
          carrier = f.carrier;
          scopes = zScopes;
          edges = zEdges;
          data = zData;
        };

        yScopes = zScopes ++ [ "b" ];
        yEdges = {
          parent =
            id:
            {
              leaf = [ "a" ];
              b = [ "top" ];
            }
            .${id} or [ ];
          include =
            id:
            {
              leaf = [ "b" ];
              a = [
                "top"
                "rival"
              ];
            }
            .${id} or [ ];
        };
        yGraph = v.scopeGraph {
          carrier = f.carrier;
          scopes = yScopes;
          edges = yEdges;
          data = zData;
        };

        # A SPLIT competition key: `c.admission` puts the two diamond arrivals in two DIFFERENT
        # groups, which is what triggers 6a's spanning check (§2.6, §2.3.3).
        splitKeyChannel = v.dataOrder {
          channel = "settings";
          keyOf = c: c.admission;
        };

        mkSplitKeyDef =
          overrides:
          v.viewDefinition (
            {
              channel = splitKeyChannel;
              relation = "import";
              root = "leaf";
              direction = "outbound";
              admission = diamondAdmission;
              order = f.flatOrder;
              wellFormed = f.admitAll;
              distance = s: s.distance + 1;
              tieSet = v.tieSets.union;
              empty = [ ];
              combine = v.combines.listAppend;
              dedup = v.dedups.none;
            }
            // overrides
          );
      in
      {
        # ★★★ O1b — THE SPLIT-KEY REFUSAL NAMES THE PRODUCER, THE ORDINAL, THE COUNT AND THE KEYS.
        # Anchored start to end: a caller resolving this reads the datum's coordinate and the
        # colliding keys, not a generic "ambiguous key" complaint.
        test-a-split-competition-key-names-the-producer-and-the-keys = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = mkSplitKeyDef { };
                graph = diamondGraph;
                marks = f.noMarks;
                orderMark = f.identityMark;
              }).value
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: channel 'settings' declares a competition key that SPLITS one element: the datum authored at scope 'top' \\(data entry 0\\) survives under 2 competition keys \\(\"'include\\*\", \"'parent\\*\"\\), so one authored declaration would contribute once per key; a competition key must be constant over an element's arrivals, and the three contribution fields that can differ across them — admission, distance, path — are path-derived$";
          };
        };

        # ★★★ O2c, fixture Z — NO DIAMOND: `top` and `rival` are genuinely distinct producers, and
        # this refusal is the ORDINARY `tieSets.refuse` — the cross-group defect never reaches it,
        # so this message must NEVER become the spanning message (that would be C1 reintroduced).
        test-o2c-fixture-z-refuses-by-the-ordinary-tieset-message = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = mkSplitKeyDef { tieSet = v.tieSets.refuse; };
                graph = zGraph;
                marks = f.noMarks;
                orderMark = f.identityMark;
              }).value
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: channel 'settings' declares tieSet 'refuse' and the competition key \"'include\\*\" survives with 2 contributions, from scopes rival, top; the declaration asked for exactly one$";
          };
        };

        # ★★★ O2c, fixture Y — Z PLUS ONE ROUTE TO `top` ALONE. One pair of edges concerning `top`
        # changes WHICH refusal fires: this is now 6a's spanning message, naming `top`'s element and
        # its two competition keys, not the ordinary tieSet count. Z's message above and this one
        # are asserted on the SAME construction differing in exactly one route, so a cross-group
        # collapse that silenced Z's refusal (den-hoag-2vzn's C1) would turn this cell from a
        # spanning refusal into a silent `n = 2` evaluation and fail here.
        test-o2c-fixture-y-refuses-by-the-spanning-message-not-the-tieset-one = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = mkSplitKeyDef { tieSet = v.tieSets.refuse; };
                graph = yGraph;
                marks = f.noMarks;
                orderMark = f.identityMark;
              }).value
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: channel 'settings' declares a competition key that SPLITS one element: the datum authored at scope 'top' \\(data entry 0\\) survives under 2 competition keys \\(\"'include\\*\", \"'parent\\*\"\\), so one authored declaration would contribute once per key; a competition key must be constant over an element's arrivals, and the three contribution fields that can differ across them — admission, distance, path — are path-derived$";
          };
        };
      };

    # ── O8d's REFUSING HALF — THE ORDER MARK IS REFUSED AT THE DEFINITION AND TAKEN AT THE
    # RELATION, plus the SEAM's own alphabet check ────────────────────────────────────────────
    #
    # ★★★ WHAT THESE GATE. M9's placement claim — the order mark arrives as an ARGUMENT to
    # `viewRelation` and NEVER as a field of the view definition — which is the whole of its
    # anti-decline guarantee. An order mark declared inside the definition would be a mark the
    # query SETS, and a query that sets its own mark can set the identity and decline. The
    # constructing half of the cell, with the live control that all three build when handed no
    # extra field, is `ci/tests/order-mark.nix`.
    #
    # ★★ AND THE FIRST TWO PIN A `required` LIST THAT MUST NOT MOVE. A build that placed the mark
    # in the definition would red them by making the refusal they assert disappear — which is the
    # wrong build this cell exists to discriminate, and the reason the lists are quoted in full
    # rather than elided to `.*`.
    flake.testsError.order-mark-refusals =
      let
        # TWO ALPHABETS, each wrapped in an INTERNALLY CONSISTENT world, so neither of the two
        # intra-object checks gen already ships has anything to say about the pair. `A` is the
        # definition's; `B` shares no letter with it.
        mkWorld = letters: rec {
          labels = v.edgeLabels { inherit letters; };
          admission = v.labelWellFormedness {
            alphabet = labels;
            expression = "(" + builtins.concatStringsSep "|" letters + ")*";
          };
          order = v.labelOrder {
            alphabet = labels;
            layers = map (l: [ l ]) letters;
            endOfPath = -1;
          };
          identity = v.labelOrder {
            alphabet = labels;
            layers = [ letters ];
            endOfPath = 0;
          };
          carrier = v.carrier {
            inherit labels;
            relations = v.relations { names = [ "import" ]; };
            relatumLabels = v.relatumLabels { names = [ "relatum-target" ]; };
            labelWellFormedness = admission;
            labelOrder = order;
            dataOrder = v.dataOrder {
              channel = "settings";
              keyOf = _: "settings";
            };
          };
        };
        A = mkWorld [
          "mandate"
          "default"
        ];
        B = mkWorld [
          "alpha"
          "beta"
        ];
        aGraph = v.scopeGraph {
          carrier = A.carrier;
          scopes = [
            "H"
            "M"
            # A scope with NO datum and NO out-edge. A query rooted here gathers nothing, which is
            # the one shape under which a refusal can go missing without any answer looking wrong.
            "Z"
          ];
          edges = {
            mandate = id: if id == "H" then [ "M" ] else [ ];
            default = _: [ ];
          };
          data = [
            {
              scope = "H";
              relation = "import";
              datum = [ "from-H" ];
            }
            {
              scope = "M";
              relation = "import";
              datum = [ "from-M" ];
            }
          ];
        };
        aDefArgs = {
          channel = "settings";
          relation = "import";
          root = "H";
          direction = "outbound";
          inherit (A) admission order;
          wellFormed = _: true;
          tieSet = v.tieSets.union;
          empty = [ ];
          combine = v.combines.listAppend;
          dedup = v.dedups.none;
        };
      in
      {
        # ★ THE DEFINITION SIDE, ARM ONE. Unchanged by the build: `orderMark` is not and must not
        # become a field of the composition, and the `required` list below is the same eleven
        # fields it named before the mark existed.
        test-o8d-the-order-mark-is-refused-as-a-field-of-the-movement-composition = {
          expr = builtins.deepSeq (v.compositions.movement (aDefArgs // { orderMark = A.identity; })) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.compositions\\.movement: field 'orderMark' is not a field of this construct; the field set is closed \\(required: admission, channel, combine, dedup, direction, empty, order, relation, root, tieSet, wellFormed\\)$";
          };
        };

        # ★ THE DEFINITION SIDE, ARM TWO — the RAW declaration, whose field set is the substrate's
        # own twelve. Also unchanged.
        test-o8d-the-order-mark-is-refused-as-a-field-of-the-view-definition = {
          expr = builtins.deepSeq (v.viewDefinition (
            aDefArgs
            // {
              channel = v.dataOrder {
                channel = "settings";
                keyOf = _: "settings";
              };
              distance = s: s.distance + 1;
              orderMark = A.identity;
            }
          )) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewDefinition: field 'orderMark' is not a field of this construct; the field set is closed \\(required: admission, channel, combine, dedup, direction, distance, empty, order, relation, root, tieSet, wellFormed\\)$";
          };
        };

        # ★★★ THE RELATION SIDE — the seam that DID open, pinned by the one message that prints the
        # `required` list. Before the build this list read `definition, graph, marks` and the mark
        # was refused here too; the cell asserts that it now reads EXACTLY those three plus
        # `orderMark`, so a build that opened the field set wider than the design, or that left it
        # shut, reds here. `contributions` is forced deliberately: `.__element` would return
        # `"viewRelation"` at exit 0 with the undeclared field still present.
        test-o8d-the-relations-field-set-is-closed-and-now-names-the-order-mark = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = v.compositions.movement aDefArgs;
                graph = aGraph;
                marks = f.noMarks;
                orderMark = A.identity;
                widen = _: true;
              }).contributions
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: field 'widen' is not a field of this construct; the field set is closed \\(required: definition, graph, marks, orderMark\\)$";
          };
        };

        # ★★★ THE SEAM'S OWN ALPHABET REFUSAL, AND IT IS NOT INHERITED FROM ANYWHERE. The two
        # checks that look like they cover this are both INTRA-OBJECT — `viewDefinition` compares a
        # definition's OWN admission against its OWN order, `carrier` a carrier's OWN members
        # against its OWN labels — and measured before this refusal existed, a definition over one
        # alphabet composed at `viewRelation` with a graph over a DISJOINT one constructed and
        # answered SILENTLY while both of those fired as controls beside it. So the order mark
        # inherits nothing here and ships its own check, in `carrier`'s "one … has one L" form.
        # ★ Its control is the cell above it and the constructing cells next door: the same call
        # with `A.identity` in place of `B.identity` answers, so this is a verdict on the ALPHABET
        # and not on the fixture.
        test-o8d-an-order-mark-over-a-foreign-alphabet-refuses-by-name = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = v.compositions.movement aDefArgs;
                graph = aGraph;
                marks = f.noMarks;
                orderMark = B.identity;
              }).contributions
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: orderMark is built over a different alphabet than the definition's `order` \\(alpha, beta vs default, mandate\\); one competition has one L$";
          };
        };

        # ★★★ AND THE SAME REFUSAL ON A QUERY THAT GATHERS NOTHING — the arm where a check can go
        # missing with NO answer looking wrong. The competition runs per group, so a materialization
        # with no groups would never force the effective order at all, and an ill-typed mark would
        # come back as `[ ]`: AN EMPTY ANSWER STANDING IN FOR A REFUSAL, which is the precise defect
        # this library's refusal discipline exists to forbid and which it has already been caught
        # committing once against itself. The cell above cannot see this arm — its fixture has
        # contributions — so without this one the guard that closes it is untested.
        # ★ CONTROL: the same root under a WELL-FORMED mark, asserted next door in
        # `ci/tests/order-mark.nix`, materializes empty rather than refusing.
        test-o8d-a-foreign-alphabet-mark-refuses-even-where-the-query-gathers-nothing = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = v.compositions.movement (aDefArgs // { root = "Z"; });
                graph = aGraph;
                marks = f.noMarks;
                orderMark = B.identity;
              }).contributions
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: orderMark is built over a different alphabet than the definition's `order` \\(alpha, beta vs default, mandate\\); one competition has one L$";
          };
        };
      };

    # ── boundedWellDefinedSchedule's OWN REFUSALS: O2 NAMES THE CYCLE, O5a NAMES NOTHING ELSE ──
    flake.testsError.schedule-refusals = {
      # ★★ O2 — THE REFUSAL NAMES THE SCC. Not merely that a declared cycle was refused, but WHICH
      # component — the same fact the historic uncatchable stack overflow could not say at all,
      # since it never reached a message.
      test-a-refused-declared-cycle-names-the-scc = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule wdsScheduleArgs) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: the declared relation has a cyclic component `admitsCycle` does not admit: \\[\\[\"child\",\"parent\"\\]\\]\\..*$";
        };
      };

      # ★★★ O5a — THE CITATION CELL. The full message, anchored start to end, so a stray occurrence
      # of the forbidden phrase anywhere in it — including the Knuth 1971 corrected per-symbol
      # algorithm this construct does NOT implement — fails this cell, not merely a substring probe.
      # P-3: the message also states its DIRECTION now — a refusal is sufficient, never necessary —
      # so this anchor moves in lockstep with `lib/ordering.nix`'s throw text.
      test-the-refusal-message-names-sloane-and-never-the-forbidden-phrase = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule wdsScheduleArgs) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: the declared relation has a cyclic component `admitsCycle` does not admit: \\[\\[\"child\",\"parent\"\\]\\]\\. Declare `admitsCycle` true for every member \\(Sloane 2009 iterate-to-fixpoint\\) or break the cycle; this refusal is not a well-definedness verdict \\(well-definedness ⟸ absence of a declared cycle, never ⟺\\)$";
        };
      };

      # ★ THE LIVE CONTROL, IN THE SAME INVOCATION: the same construct, the declared cycle removed,
      # does not refuse. Without it the two cells above are consistent with a construct that
      # refuses whatever it is handed and a message that never varies with its input.
      test-control-the-same-construct-with-the-cycle-broken-does-not-refuse = {
        expr =
          (v.boundedWellDefinedSchedule (
            wdsScheduleArgs
            // {
              declaredDependencies = wdsDeclaredAcyclic;
            }
          )).condensation.sccs;
        expected = [
          [ "parent" ]
          [ "child" ]
        ];
      };

      # ══ C-1 — `nodes` MUST CONTAIN EVERY ENDPOINT OF THE DECLARED RELATION; CHECKED, NOT
      # ASSUMED. Three arms, one per landing-gate finding: an endpoint outside `nodes` is refused
      # BY NAME rather than silently narrowing the partition or reaching gen-graph's own
      # partitioner for a node it never registered, which aborts uncatchably
      # (`attribute … missing`, `lib/partition.nix`).

      # Before this repair: `nodes = [ "other" ]` with the declared 2-cycle SILENTLY ADMITTED —
      # `{ success = true; sccs = [ [ "other" ] ]; }` — because `graph.condensation` never saw
      # `child` or `parent` at all.
      test-nodes-omitting-every-endpoint-of-the-declared-relation-names-them-both = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            nodes = [ "other" ];
            admitsCycle = _: false;
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'nodes' does not contain the declared relation's endpoint\\(s\\) child, parent; ADR-0008 §3's precondition is a declared edge set complete at registration, so every source and target `declaredDependencies` names must be a member of `nodes`$";
        };
      };

      # Before this repair: `nodes = [ "child" ]` reached gen-graph's own partitioner for `parent`,
      # a node it never registered, and aborted UNCATCHABLY.
      test-nodes-omitting-one-endpoint-of-a-declared-cycle-names-it = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            nodes = [ "child" ];
            admitsCycle = _: false;
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'nodes' does not contain the declared relation's endpoint\\(s\\) parent; ADR-0008 §3's precondition is a declared edge set complete at registration, so every source and target `declaredDependencies` names must be a member of `nodes`$";
        };
      };

      # `index`'s keys are grouped by SOURCE, so a `nodes` built from `attrNames index` alone omits
      # every sink — the same uncatchable abort as above, this time for a relation that has no
      # cycle at all: containment is checked before the partition is ever forced.
      test-nodes-derived-from-the-index-keys-alone-omits-a-sink-and-is-named = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            nodes = builtins.attrNames wdsDeclaredAcyclic.index;
            declaredDependencies = wdsDeclaredAcyclic;
            admitsCycle = _: false;
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'nodes' does not contain the declared relation's endpoint\\(s\\) parent; ADR-0008 §3's precondition is a declared edge set complete at registration, so every source and target `declaredDependencies` names must be a member of `nodes`$";
        };
      };

      # ══ C-1 — `admitsCycle` MUST BE A FUNCTION; A NON-FUNCTION IS NAMED rather than left to
      # abort uncatchably inside `builtins.all` ══
      test-admitsCycle-not-a-function-is-named = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            admitsCycle = "not-a-function";
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' must be a function from a node identifier to a bool \\(`isRegistered`'s shape — the membership authority `mkNodeRef` itself takes\\); received a string$";
        };
      };

      # ══ C-3 — `builtins.isFunction` ABOVE CLOSES ONLY THE NON-FUNCTION CASE; A FUNCTION OF THE
      # WRONG RETURN TYPE OR THE WRONG ARITY STILL SATISFIED IT AND PREVIOUSLY REACHED
      # `builtins.all` UNCATCHABLY. Measured before this repair, one run each, with `tryEval`:
      # `admitsCycle = _: "yes"` unwound THROUGH `tryEval` to `error: expected a Boolean but found
      # a string: "yes"`; `admitsCycle = _: _: true` unwound to `error: expected a Boolean but
      # found a function`. Both are now named refusals, caught here the same way as the
      # non-function case above, because `illTypedAdmissions` checks the APPLIED result rather than
      # the function's shape (`den-hoag-g8lo`; see `lib/ordering.nix`'s header on the same guard).
      test-admitsCycle-wrong-return-type-is-named = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            admitsCycle = _: "yes";
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' must return a bool for every node identifier; for `child` it returned a string$";
        };
      };

      # The wrong-arity case is the same guard for UNDER-APPLICATION only: an under-applied
      # `id -> id -> bool` forces to a lambda, not a bool, at the same site and is refused the
      # same way a wrong return type is. This does NOT close arity generally: a PATTERN FORMAL
      # (`{ x }: true`, `{ x, ... }: true`) still satisfies `isFunction` and aborts UNCATCHABLY
      # computing `r`, before this check ever runs — pinned as a falsifier below rather than
      # claimed closed.
      test-admitsCycle-wrong-arity-is-named = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            admitsCycle = _: _: true;
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' must return a bool for every node identifier; for `child` it returned a lambda$";
        };
      };

      # ══ C-4 RESIDUE — A PATTERN FORMAL PASSES THE `isFunction` DOOR AND ABORTS UNCATCHABLY
      # BUILDING `admissions`, ESCAPING `builtins.tryEval` (den-hoag-6poeg landing gate 3, C-4).
      # This is NOT a `ThrownError`: Nix's own evaluator raises it computing `a.admitsCycle n`,
      # before `illTypedAdmissions`' bool check runs, so no `refuse` call in this library names it.
      # The
      # message is unanchored on purpose — it is the evaluator's own rendering, not authored text
      # this library controls, so pinning it end-to-end would freeze on an evaluator-version detail
      # rather than on this construct's behaviour.
      test-admitsCycle-pattern-formal-aborts = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs // { admitsCycle = { x }: true; }
        )) true;
        expectedError = {
          type = "TypeError";
          msg = "expected a set but found a string";
        };
      };

      # ══ C-5 — THE APPLIED-RESULT CHECK IS TOTAL OVER `nodes`, NOT CONDITIONAL ON A CYCLE
      # EXISTING (den-hoag-6poeg landing gate 4, C-5) ══
      # ★ THE FIXTURE IS THE WHOLE POINT OF THIS CELL. Every other `admitsCycle` cell above rides
      # `wdsScheduleArgs`, whose `declaredDependencies` is `wdsDeclaredCyclic`; this one overrides
      # it to `wdsDeclaredAcyclic`. Before this repair the check lived inside `badSccs`, behind
      # `isCyclicScc scc &&`, and Nix's `&&` short-circuits — so on an acyclic declared relation
      # `admitsCycle` was NEVER APPLIED, and every ill-typed authority was admitted GREEN. Measured
      # on this exact input at `f74c39da`: the construct RETURNED A SCHEDULE. Four successive
      # landing gates could not see it because `wdsDeclaredAcyclic` was only ever paired with a
      # well-typed authority — the FIXTURE PAIRING, not the assertions, is what hid it. The refusal
      # text below is byte-identical to the cyclic-fixture cell above, and that identity IS the
      # assertion: whether an ill-typed authority is caught no longer depends on the shape of the
      # declared relation, which is data the caller may not control.
      test-admitsCycle-wrong-return-type-is-named-on-an-acyclic-relation = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            declaredDependencies = wdsDeclaredAcyclic;
            admitsCycle = _: "yes";
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' must return a bool for every node identifier; for `child` it returned a string$";
        };
      };

      # ══ C-7 — THE CHECK REACHES PAST ELEMENT 0 OF `nodes` (den-hoag-6poeg landing gate 5) ══
      # ★ THE FIXTURE NAMES `parent`, AND THAT IS THE WHOLE CELL. Every other `admitsCycle` cell
      # hands in an authority that is ill-typed for EVERY node, so all of them name `child` —
      # element 0 in every fixture here. Narrowing `illTypedAdmissions`' domain to
      # `[ (builtins.head nodes) ]` would leave every cell in BOTH suites reading green at a red
      # state — this cell is the only instrument in the repository that can see that, which is
      # why `filter` over the whole of `nodes` — and not `builtins.all`, and not the first
      # non-bool — is the mechanism the spec's §2.7.1 row 6 requires.
      test-admitsCycle-ill-typed-on-a-later-node-is-named = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            declaredDependencies = wdsDeclaredAcyclic;
            admitsCycle = n: if n == "child" then false else "yes";
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' must return a bool for every node identifier; for `parent` it returned a string$";
        };
      };
    };
  };
}
