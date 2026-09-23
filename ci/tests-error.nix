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
      # ★ NOT A REFUSAL THIS LIBRARY CHOSE — den-hoag-kunjm's held abort, pinned so that
      # den-hoag-eunp3's address change is seen NOT to remove it: a function-bearing datum that
      # also carries string context now reaches the context abort instead of the lambda abort.
      # kunjm's landing flips this cell.
      test-a-function-bearing-datum-with-string-context-still-reaches-the-context-abort = {
        expr =
          let
            m = { config, ... }: { };
            p = builtins.toFile "eunp3-ctx" "x";
            datum = scope: {
              inherit scope;
              relation = "import";
              datum = [
                m
                p
              ];
            };
            r = v.viewRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                dedup = v.dedups.byDatum;
              };
              graph = v.scopeGraph {
                inherit (f) carrier scopes edges;
                data = [
                  (datum "inc")
                  (datum "mid")
                ];
              };
              marks = f.noMarks;
              orderMark = f.identityMark;
            };
          in
          builtins.length r.contributions;
        expectedError = {
          type = "EvalError";
          msg = "is not allowed to refer to a store path";
        };
      };

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

      # ★ STEP 9 READS THE ARM'S ASSOCIATIVITY DECLARATION. The fold is a balanced bracketing,
      # which only associativity licenses, so an arm declaring `associative = false` is refused by
      # name rather than re-bracketed into a different answer. The arm here is hand-built (no
      # whitelisted arm is non-associative); the control above is the same fixture with the
      # declaration intact.
      test-a-non-associative-combine-is-refused-at-the-fold = {
        expr =
          builtins.deepSeq
            (f.mkRelation {
              definition = f.mkDefinition {
                order = f.flatOrder;
                combine = v.combines.listAppend // {
                  associative = false;
                };
              };
            }).value
            true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.foldCombine: the combine arm 'listAppend' does not declare associative = true.*$";
        };
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

        # p79do C1: the same split-key refusal, its definition's constructor-made `name` forged to a
        # lambda. The render goes through `renderSubject`, so the refusal stays named and catchable.
        test-a-forged-definition-name-renders-a-lambda-at-a-split-key = {
          expr =
            builtins.deepSeq
              (v.viewRelation {
                definition = mkSplitKeyDef { } // {
                  name = x: x;
                };
                graph = diamondGraph;
                marks = f.noMarks;
                orderMark = f.identityMark;
              }).value
              true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.viewRelation: channel <a lambda> declares a competition key that SPLITS one element: the datum authored at scope 'top'.*$";
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

    # ── THE OTHER HALF OF THE ALPHABET SEAM — THE DEFINITION AGAINST THE GRAPH ────────────────
    #
    # ★★★ WHAT THESE GATE, AND IT IS NOT THE ORDER MARK. The section above pins the mark against the
    # DEFINITION; these pin the DEFINITION against the GRAPH it is composed with, and neither
    # implies the other — the cells below hand a mark that AGREES with the definition, so the mark's
    # check cannot fire and only this one can. Measured before it existed: a definition over one
    # alphabet composed with a graph over a disjoint one CONSTRUCTED AND ANSWERED, `contributions`
    # carrying the root's own datum at exit 0, while `viewDefinition`'s intra-object check,
    # `carrier`'s intra-object check and the mark check above all fired as controls beside it.
    #
    # ★★ THE ANSWER IT GAVE IS WHY THIS IS A DEFECT AND NOT A MISSING CONVENIENCE.
    # `labelWellFormedness` refuses a literal outside its OWN alphabet, so a foreign admission
    # expression is perfectly well-formed over letters the graph does not carry and matches NO edge
    # of it: the walk reaches the root and stops, and the result is the root's own datum wearing the
    # shape of a gather. There is no reading of that answer in which a caller learns anything.
    #
    # ★ CONTROL, IN `ci/tests/relation.nix`: the same two calls with the graph's own alphabet in
    # place of the foreign one materialize — `[ "root" ]` at `root` and EMPTY at `void` — so these
    # are verdicts on the ALPHABET and not on the fixture or on the empty gather.
    flake.testsError.alphabet-seam-refusals =
      let
        # A world sharing NO letter with `f`'s (`include`, `parent`), internally consistent so that
        # neither intra-object check has anything to say about it. It is never built into a carrier:
        # the point is a DEFINITION over it, composed with `f.graph`, which is over the other.
        foreignLabels = v.edgeLabels {
          letters = [
            "alpha"
            "beta"
          ];
        };
        foreignDef =
          root:
          f.mkDefinition {
            inherit root;
            admission = v.labelWellFormedness {
              alphabet = foreignLabels;
              expression = "(alpha|beta)*";
            };
            order = v.labelOrder {
              alphabet = foreignLabels;
              layers = [
                [ "alpha" ]
                [ "beta" ]
              ];
              endOfPath = -1;
            };
          };
        # ★★★ THE MARK IS THE DEFINITION'S OWN, AND THE CELL IS WORTHLESS OTHERWISE. Handing
        # `f.identityMark` — the identity over the GRAPH's L — makes the section above's check fire
        # instead, and MEASURED that way against the library before this seam was closed, the cells
        # went red on the ORDER MARK's message rather than on a silent answer. A cell built that way
        # is green on any build that merely reorders two guards, and it never once sees the defect
        # it is named for. The mark therefore agrees with the definition, the mark check cannot
        # fire, and what these cells refuse is the definition against the graph and nothing else.
        foreignMark = v.labelOrder {
          alphabet = foreignLabels;
          layers = [
            [
              "alpha"
              "beta"
            ]
          ];
          endOfPath = 0;
        };
        run =
          root:
          builtins.deepSeq
            (v.viewRelation {
              definition = foreignDef root;
              graph = f.voidGraph;
              marks = f.noMarks;
              orderMark = foreignMark;
            }).contributions
            true;
        # `quote` sorts, so both alphabets print sorted regardless of how they were declared.
        msg = "^gen-view\\.viewRelation: the definition's alphabet is not the graph's \\(alpha, beta vs include, parent\\); one composition has one L$";
      in
      {
        # THE GATHERING ARM. `root` holds a datum, so before this refusal existed the call answered
        # `[ [ "root" ] ]` at exit 0 — a short, plausible, entirely wrong answer.
        test-a-definition-over-an-alphabet-the-graph-does-not-carry-refuses-by-name = {
          expr = run "root";
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };

        # ★★★ AND THE ARM A CARELESS LANDING OMITS — the query that GATHERS NOTHING. Competition
        # runs per group, so a materialization with no groups never forces the effective order at
        # all, and a guard bound there alone would let this call answer `[ ]`: AN EMPTY ANSWER
        # STANDING IN FOR A REFUSAL, which is the precise defect this library's refusal discipline
        # exists to forbid and which it has been caught committing against itself once already. The
        # cell above cannot see this arm — its fixture has contributions.
        # ★ CONTROL: `void` under a definition over the graph's OWN alphabet materializes EMPTY
        # rather than refusing (`ci/tests/relation.nix`), so the refusal here is a verdict on the
        # alphabet and not on the absent gather.
        test-a-foreign-alphabet-definition-refuses-even-where-the-query-gathers-nothing = {
          expr = run "void";
          expectedError = {
            type = "ThrownError";
            inherit msg;
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

    # ── A REFUSAL RENDERS ITS SUBJECT TOTALLY (ADR-0025 item 1) ──
    # One cell per refusal site whose message renders a caller value. Each subject carries a lambda
    # (or a cyclic value), which `toJSON` and string interpolation both abort on PAST `tryEval`: before
    # `renderValue`/`renderSubject`, every cell here read `TypeError` (the cyclic one `Error`) where a
    # named `ThrownError` belongs. Each pins the refusal's site prefix, its wording and the rendered
    # type, anchored. The `forged-*` cells hand in an attrset carrying a genuine tag and a field no
    # constructor would produce: a tag is a claim about how an element was built, not a proof of it,
    # so a render resting on the constructor goes through the renderer like any other caller value.
    flake.testsError.render-totality =
      let
        fn = x: x;
        cyc =
          let
            c = {
              self = c;
            };
          in
          c;
        vd = over: v.viewDefinition (f.definitionArgs // over);
        engine = {
          query = _: [ ];
          queryReverse = _: [ ];
        };
        forged = el: arm: {
          __element = el;
          inherit arm;
        };
        notString = l: !(builtins.isString l);
        cell = expr: msg: {
          expr = builtins.deepSeq expr true;
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };
      in
      {
        test-choice-renders-a-lambda =
          cell
            (v.placement.place {
              mode = fn;
              path = [ ];
              name = "x";
              value = 1;
            })
            "^gen-view\\.place: field 'mode' is <a lambda>, which is not one of the declared arms \\(merge, nest, nest-verbatim\\)$";
        test-direction-renders-a-lambda =
          cell
            (vd {
              direction = fn;
            })
            "^gen-view\\.viewDefinition: field 'direction' is <a lambda>, which is not one of the declared arms \\(inbound, outbound\\)$";
        test-empty-renders-a-lambda-bearing-list =
          cell
            (vd {
              empty = [ fn ];
            })
            "^gen-view\\.viewDefinition: field 'empty' is <a list>, which is not the unit of the declared combine arm 'listAppend' \\(\\[\\]\\).*$";
        test-element-tag-renders-a-lambda =
          cell
            (vd {
              tieSet = {
                __element = fn;
              };
            })
            "^gen-view\\.viewDefinition: field 'tieSet' is not a tieSet carrier element \\(found an attrset tagged <a lambda>\\).*$";
        test-element-tag-renders-a-cyclic-value =
          cell
            (vd {
              tieSet = {
                __element = cyc;
              };
            })
            "^gen-view\\.viewDefinition: field 'tieSet' is not a tieSet carrier element \\(found an attrset tagged <a set>\\).*$";
        test-discipline-flag-renders-a-lambda =
          cell
            (v.referenceResolution {
              inherit engine;
              name = "r";
              wellFormed = _: true;
              project = n: n;
              localShadowsImport = true;
              importShadowsParent = fn;
              transitiveImports = true;
            })
            "^gen-view\\.referenceResolution: field 'importShadowsParent' is <a lambda>, which is not a boolean.*$";
        test-transitive-renders-a-lambda = cell (v.neededBy {
          inherit engine;
          name = "r";
          wellFormed = _: true;
          project = n: n;
          transitive = fn;
        }) "^gen-view\\.neededBy: field 'transitive' is <a lambda>, which is not a boolean.*$";
        test-forged-tieSet-arm-renders-a-lambda =
          cell
            (vd {
              tieSet = forged "tieSet" fn;
            })
            "^gen-view\\.viewDefinition: field 'tieSet' names <a lambda>, which is not one of the declared arms.*$";
        test-forged-combine-arm-renders-a-lambda =
          cell
            (vd {
              combine = forged "combine" fn;
            })
            "^gen-view\\.viewDefinition: field 'combine' names <a lambda>, which is not one of the whitelisted arms.*$";
        test-forged-combine-unit-renders-a-lambda =
          cell
            (vd {
              combine = {
                __element = "combine";
                arm = "listAppend";
                setSemilattice = false;
                unit = fn;
                associative = true;
              };
            })
            "^gen-view\\.viewDefinition: field 'empty' is \\[\\], which is not the unit of the declared combine arm 'listAppend' \\(<a lambda>\\).*$";
        test-forged-dedup-arm-renders-a-lambda =
          cell
            (vd {
              dedup = forged "dedup" fn;
            })
            "^gen-view\\.viewDefinition: field 'dedup' names <a lambda>, which is not one of the declared arms.*$";
        test-datum-scope-renders-a-lambda =
          cell
            (v.scopeGraph {
              inherit (f) carrier scopes edges;
              data = [
                {
                  scope = fn;
                  relation = "import";
                  datum = [ "x" ];
                }
              ];
            })
            "^gen-view\\.scopeGraph: a datum is filed at scope <a lambda>, which is not a scope of this graph.*$";
        test-datum-relation-renders-a-lambda = cell (v.scopeGraph
          {
            inherit (f) carrier scopes edges;
            data = [
              {
                scope = "root";
                relation = fn;
                datum = [ "x" ];
              }
            ];
          }
        ) "^gen-view\\.scopeGraph: a datum is filed under relation <a lambda>, which is not a name in R.*$";
        test-relationEntries-renders-a-lambda = cell (v.relationEntries {
          graph = f.graph;
          scope = "leaf";
          relation = fn;
          wellFormed = _: true;
        }) "^gen-view\\.relationEntries: <a lambda> is not a name in R.*$";
        test-target-channel-renders-a-lambda =
          cell
            (v.writesOf {
              inherit (f) relation;
              target = v.placement.targets.root {
                scope = "leaf";
                channel = fn;
              };
              mode = "merge";
            })
            "^gen-view\\.writesOf: the target names channel <a lambda> but the view relation is named 'settings'.*$";
        test-forged-tieSet-order-renders-a-lambda-bearing-list =
          cell
            (f.mkRelation {
              definition = f.mkDefinition {
                tieSet = {
                  __element = "tieSet";
                  arm = "orderedFold";
                  order = [ fn ];
                };
              };
            }).value
            "^gen-view\\.viewRelation: channel 'settings' declares tieSet 'orderedFold' whose declared order \\(<a list>\\) does not rank the contributing scope 'inc'.*$";

        # ── C1: A RENDER RESTING ON HOW AN ELEMENT WAS BUILT ──
        # Each string below is a string on every genuine path only because a constructor made it one.
        # The forged element keeps the genuine tag and replaces one constructor-made field.
        test-forged-relation-name-renders-a-lambda-at-writesOf =
          cell
            (v.writesOf {
              relation = {
                __element = "viewRelation";
                name = fn;
              };
              target = v.placement.targets.root {
                scope = "leaf";
                channel = "settings";
              };
              mode = "merge";
            })
            "^gen-view\\.writesOf: the target names channel 'settings' but the view relation is named <a lambda>;.*$";
        test-forged-definition-name-renders-a-lambda-at-a-refused-tie =
          cell
            (f.mkRelation {
              definition =
                f.mkDefinition {
                  order = f.flatOrder;
                  tieSet = v.tieSets.refuse;
                }
                // {
                  name = fn;
                };
            }).value
            "^gen-view\\.viewRelation: channel <a lambda> declares tieSet 'refuse' and the competition key \"settings\" survives with 2 contributions, from scopes inc, mid.*$";
        test-forged-definition-name-renders-a-lambda-at-an-unranked-scope =
          cell
            (f.mkRelation {
              definition =
                f.mkDefinition {
                  order = f.flatOrder;
                  tieSet = v.tieSets.orderedFold { order = [ "mid" ]; };
                }
                // {
                  name = fn;
                };
            }).value
            "^gen-view\\.viewRelation: channel <a lambda> declares tieSet 'orderedFold' whose declared order \\(mid\\) does not rank the contributing scope 'inc'.*$";
        test-forged-combine-arm-renders-a-lambda-at-the-fold =
          cell
            (f.mkRelation {
              definition = f.definition // {
                combine = f.definition.combine // {
                  arm = fn;
                  associative = false;
                };
              };
            }).value
            "^gen-view\\.foldCombine: the combine arm <a lambda> does not declare associative = true;.*$";
        test-forged-alphabet-letter-renders-a-lambda-at-labelOrder = cell (v.labelOrder {
          alphabet = f.labels // {
            letters = [
              "parent"
              "include"
              fn
            ];
          };
          layers = [
            [ "include" ]
            [ "parent" ]
          ];
          endOfPath = -1;
        }) "^gen-view\\.labelOrder: letter <a lambda> is not ranked;.*$";
        test-forged-relation-name-renders-a-lambda-at-the-carrier = cell (v.carrier {
          labels = f.labels // {
            member = _: true;
          };
          relations = f.relations // {
            names = [ fn ];
          };
          relatumLabels = f.roles;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        }) "^gen-view\\.carrier: <a lambda> is both a letter of L and a name in R;.*$";
        test-forged-role-label-renders-a-lambda-against-the-letters = cell (v.carrier {
          labels = f.labels // {
            member = notString;
          };
          inherit (f) relations;
          relatumLabels = f.roles // {
            names = [ fn ];
          };
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        }) "^gen-view\\.carrier: <a lambda> is both a letter of L and a relatum label in Λ;.*$";
        test-forged-role-label-renders-a-lambda-against-the-relations = cell (v.carrier {
          inherit (f) labels;
          relations = f.relations // {
            member = notString;
          };
          relatumLabels = f.roles // {
            names = [ fn ];
          };
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        }) "^gen-view\\.carrier: <a lambda> is both a name in R and a relatum label in Λ;.*$";

        # ── den-hoag-gen-view-refusal-sort-abort-tm84v: the name to report is chosen without a sort ──
        # `lessThan` aborts past `tryEval` on two lambdas, so before `sortNames` each of these read
        # `cannot compare a function with a function` where the refusal above belongs. Two forged
        # names each, which is the least that reaches a comparison.
        test-two-forged-alphabet-letters-reach-labelOrder = cell (v.labelOrder {
          alphabet = f.labels // {
            letters = [
              "parent"
              "include"
              fn
              fn
            ];
          };
          layers = [
            [ "include" ]
            [ "parent" ]
          ];
          endOfPath = -1;
        }) "^gen-view\\.labelOrder: letter <a lambda> is not ranked;.*$";
        test-two-forged-relation-names-reach-the-carrier = cell (v.carrier {
          labels = f.labels // {
            member = _: true;
          };
          relations = f.relations // {
            names = [
              fn
              fn
            ];
          };
          relatumLabels = f.roles;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        }) "^gen-view\\.carrier: <a lambda> is both a letter of L and a name in R;.*$";
        test-two-forged-role-labels-reach-the-letters = cell (v.carrier {
          labels = f.labels // {
            member = notString;
          };
          inherit (f) relations;
          relatumLabels = f.roles // {
            names = [
              fn
              fn
            ];
          };
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        }) "^gen-view\\.carrier: <a lambda> is both a letter of L and a relatum label in Λ;.*$";
        test-two-forged-role-labels-reach-the-relations = cell (v.carrier {
          inherit (f) labels;
          relations = f.relations // {
            member = notString;
          };
          relatumLabels = f.roles // {
            names = [
              fn
              fn
            ];
          };
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        }) "^gen-view\\.carrier: <a lambda> is both a name in R and a relatum label in Λ;.*$";
        test-two-forged-order-letters-reach-the-alphabet-seam =
          cell
            (f.mkRelation {
              definition = f.definition // {
                order = f.order // {
                  alphabet = f.labels // {
                    letters = [
                      fn
                      fn
                    ];
                  };
                };
              };
            }).value
            "^gen-view\\.viewRelation: the definition's alphabet is not the graph's \\(<a list> vs include, parent\\); one composition has one L$";

        # ── den-hoag-gen-view-fields-attrnames-abort-txc33: `fields` refuses a non-attrset by name ──
        # `attrNames` over a function aborts past `tryEval`, so before the `isAttrs` arm every
        # construct gated by `fields` did on a non-attrset argument.
        test-a-non-attrset-argument-is-refused-at-writesOf = cell (v.writesOf fn) "^gen-view\\.writesOf: the argument must be an attrset of this construct's fields, not a lambda \\(required: mode, relation, target\\)$";
        test-a-non-attrset-argument-is-refused-at-viewDefinition = cell (v.viewDefinition fn) "^gen-view\\.viewDefinition: the argument must be an attrset of this construct's fields, not a lambda.*$";
      };

    # ── A VALUE-PATH COMPARATOR SEES ONLY ITS DOMAIN (ADR-0025 item 1) ──
    # Step 4's `<` over distances and `effectiveOrder`'s `lexLess` over ranks are `<` on ints, and a
    # non-int operand aborts there PAST `tryEval`. Each operand is checked where it enters against a
    # contract gen-view already states: the distance rule is `{ distance; from; label; to; } → int`
    # (`viewDefinition`), and a label order ranks L̂ by ints (`labelOrder`). Before the checks, each
    # refusal cell below read `EvalError`, and the string distance was a VALUE compared
    # lexicographically. The rank cells hand in a genuine order with `rankOf` replaced: the tag
    # survives `//`, so a tag is a claim and not proof.
    flake.testsError.value-comparator-refusals =
      let
        fn = x: x;
        cell = expr: msg: {
          expr = builtins.deepSeq expr true;
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };
        # ci/tests/relation.nix's diamond: `a` is reached from `d` in one hop and in two, in one
        # derivative state, so step 4's projection compares the two arrivals' distances.
        dLabels = v.edgeLabels { letters = [ "parent" ]; };
        dAdmission = v.labelWellFormedness {
          alphabet = dLabels;
          expression = "parent*";
        };
        dOrder = v.labelOrder {
          alphabet = dLabels;
          layers = [ [ "parent" ] ];
          endOfPath = -1;
        };
        dKey = v.dataOrder {
          channel = "d";
          keyOf = c: c.scope;
        };
        diamondUnder =
          distance:
          v.viewRelation {
            definition = v.viewDefinition {
              channel = dKey;
              relation = "import";
              root = "d";
              direction = "outbound";
              admission = dAdmission;
              order = dOrder;
              wellFormed = f.admitAll;
              inherit distance;
              tieSet = v.tieSets.union;
              empty = [ ];
              combine = v.combines.listAppend;
              dedup = v.dedups.none;
            };
            graph = v.scopeGraph {
              carrier = v.carrier {
                relatumLabels = f.roles;
                labels = dLabels;
                labelWellFormedness = dAdmission;
                labelOrder = dOrder;
                dataOrder = dKey;
                relations = v.relations { names = [ "import" ]; };
              };
              scopes = [
                "a"
                "b"
                "d"
              ];
              edges.parent =
                id:
                {
                  d = [
                    "b"
                    "a"
                  ];
                  b = [ "a" ];
                }
                .${id} or [ ];
              data = f.authored {
                a = [
                  {
                    relation = "import";
                    datum = [ "a" ];
                  }
                ];
              };
            };
            marks = f.noMarks;
            orderMark = v.labelOrder {
              alphabet = dLabels;
              layers = [ [ "parent" ] ];
              endOfPath = 0;
            };
          };
      in
      {
        # LIVE CONTROL: under an int rule the diamond materializes, and the projection keeps the
        # one-hop arrival.
        test-control-the-diamond-materializes-under-hop-count = {
          expr = map (c: c.distance) (diamondUnder (s: s.distance + 1)).contributions;
          expected = [ 1 ];
        };
        test-a-distance-rule-returning-a-lambda-is-refused-by-name =
          cell (diamondUnder (_: fn)).value
            "^gen-view\\.viewRelation: channel 'd' declares a distance rule that returned <a lambda> .*$";
        # A string is the case that used to answer: `"x"` against `1` aborted, but two strings
        # compared lexicographically, so "10" ranked before "9".
        test-a-distance-rule-returning-a-string-is-refused-by-name =
          cell (diamondUnder (s: if builtins.isInt s.distance then "x" else 1)).value
            "^gen-view\\.viewRelation: channel 'd' declares a distance rule that returned \"x\" .*$";
        test-a-forged-order-mark-rank-is-refused-by-name =
          cell
            (f.mkRelation {
              orderMark = f.identityMark // {
                rankOf = l: if l == "$" then 0 else fn;
              };
            }).value
            "^gen-view\\.viewRelation: orderMark ranks '[a-z]+' at <a lambda>.*$";
        test-a-forged-definition-order-rank-is-refused-by-name =
          cell
            (f.mkRelation {
              definition = f.definition // {
                order = f.order // {
                  rankOf = _: fn;
                };
              };
            }).value
            "^gen-view\\.viewRelation: the definition's order ranks '[a-z]+' at <a lambda>.*$";
      };
  };
}
