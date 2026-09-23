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
    # ── A KEY COMPONENT OF THE WRONG SHAPE IS REFUSED BY NAME ──
    # `tupleKey` guards by POSITION: every component is a string except a tuple's path, which is a
    # list of strings. The shapes are what keep the target arms apart, so a guard admitting either
    # shape anywhere lets a list-valued scope forge an output cell, or a string-valued path forge a
    # root one. Without the guard a non-string also aborts uncatchably inside interpolation.
    flake.testsError.key-encoding =
      let
        refused = expr: msg: {
          expr = builtins.deepSeq expr true;
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };
        forgedStringPath = {
          __element = "target";
          arm = "output";
          path = "x/y";
        };
      in
      {
        test-a-non-string-cell-component-is-refused-by-name = refused (v.cell 1 "c"
          "input"
        ) "^gen-view\\.cell: a key component is 1; a name in a key must be a string$";
        test-a-non-string-path-segment-is-refused-by-name = refused (v.placement.pathKey [
          1
        ]) "^gen-view\\.pathKey: a key component is 1; a name in a key must be a string$";
        # A list where a cell's scope belongs would otherwise key equal to the output write of the
        # path `[ "x/y" ]`: `[ "out", [ "x/y" ], "output" ]` both ways.
        test-a-list-in-a-cell-name-position-is-refused-by-name = refused (v.cell "out" [
          "x/y"
        ] "output") "^gen-view\\.cell: a key component is \\[\"x/y\"\\]; a name in a key must be a string$";
        # A string where an output write's path belongs would otherwise key equal to the root
        # target ⟨out, x/y⟩'s output cell.
        test-a-string-in-a-write-path-position-is-refused-by-name = refused (v.writesOf {
          inherit (f) relation;
          target = forgedStringPath;
          mode = "merge";
        }) "^gen-view\\.writesOf: a key component is \"x/y\"; a path in a key must be a list of strings$";
        # ★ `sourceKey` IS JSON-ENCODED BUT DELIBERATELY UNGUARDED (see `lib/placement.nix`): a
        # non-string must abort exactly as it did under interpolation, not be silently keyed. A
        # bare `toJSON` would key `[1,"import"]` and this cell would see no error at all.
        test-a-non-string-source-scope-still-aborts-as-before = {
          expr = builtins.deepSeq (v.placement.sourceKey {
            scope = 1;
            relation = "import";
          }) true;
          expectedError.type = "TypeError";
        };
      };
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

      # A non-string scope is refused by name, where the index read would abort past `tryEval`.
      test-a-non-string-scope-is-named = {
        expr = builtins.deepSeq (v.relationEntries {
          graph = f.graph;
          scope = 42;
          relation = "import";
          wellFormed = f.admitAll;
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.relationEntries: scope is 42; a scope is named by a string$";
        };
      };

      # A label outside L̂ is refused by name, where the rank read would abort past `tryEval`.
      test-precedes-names-an-unknown-label = {
        expr = f.order.precedes "nope" "parent";
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.labelOrder: 'nope' is not a label of L̂ \\(include, parent, or `\\$`\\)$";
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

      # The LEAST duplicate is named, and it is not the first one met: `c` repeats before `b`
      # does. `strings` counts by an attrset keyed once, and `attrNames` is already sorted.
      test-a-duplicate-scope-names-the-least-duplicate = {
        expr = builtins.deepSeq (v.scopeGraph {
          carrier = f.carrier;
          scopes = [
            "r"
            "c"
            "b"
            "c"
            "a"
            "b"
          ];
          edges = { };
          data = [ ];
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.scopeGraph: scopes names 'b' more than once$";
        };
      };

      # Two copies of one name differing only in string context are one name twice: `==` ignores
      # context, so the count's key is the context-discarded text, and a keyed count that kept the
      # context would abort uncatchably on the store path instead of naming the duplicate.
      test-a-duplicate-scope-differing-only-in-context-is-named = {
        expr = builtins.deepSeq (v.scopeGraph {
          carrier = f.carrier;
          scopes = [
            "r"
            "${builtins.substring 0 0 (toString (builtins.toFile "ar4kb-ctx" "x"))}zz"
            "zz"
          ];
          edges = { };
          data = [ ];
        }) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.scopeGraph: scopes names 'zz' more than once$";
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
        expected = [ "[\"inc\",\"settings\",\"input\"]" ];
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
      # with named formals (`{ x }: true`) is refused at the door by `formalsOf`, and one that
      # `functionArgs` cannot see (`{ ... }: true`) still satisfies `isFunction` and aborts
      # UNCATCHABLY computing `r`, before this check ever runs — both pinned below.
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

      # ══ C-4 — A PATTERN FORMAL. A NON-EMPTY formal set is refused by name at the door
      # (`formalsOf`, den-hoag-0gpyq): `admitsCycle` is applied to a string, so it can never apply.
      # The RESIDUE is `{ ... }:`, which `functionArgs` reports as `{ }`: it passes the
      # `isFunction` door and aborts UNCATCHABLY building `admissions`, escaping `builtins.tryEval`
      # (den-hoag-6poeg landing gate 3, C-4). That is NOT a `ThrownError`: Nix's own evaluator
      # raises it computing `a.admitsCycle n`, before `illTypedAdmissions`' bool check runs, so the
      # falsifier's message is unanchored on purpose — it is the evaluator's own rendering, not
      # authored text this library controls.
      test-admitsCycle-pattern-formal-is-named = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs // { admitsCycle = { x }: true; }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' destructures an attrset \\(formals: x\\); .*$";
        };
      };
      test-admitsCycle-ellipsis-formal-aborts = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs // { admitsCycle = { ... }: true; }
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

      # A FORGED relation carrying a non-string endpoint is still refused by the containment
      # message. `mkNodeRef` refuses a non-string, so only a value wearing gen-graph's tag reaches
      # this: `nodeIndex ? ${…}` on an int would abort on the coercion, and the `isString` guard in
      # `missingEndpoints` answers "not a member" as `elem` did.
      test-a-forged-non-string-endpoint-is-refused-by-the-containment-message = {
        expr = builtins.deepSeq (v.boundedWellDefinedSchedule (
          wdsScheduleArgs
          // {
            declaredDependencies = {
              _type = "gen-graph/declared-edges";
              index = {
                child = [ 7 ];
              };
              dependencies = _: [ ];
            };
          }
        )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.boundedWellDefinedSchedule: field 'nodes' does not contain the declared relation's endpoint\\(s\\) <a list>; .*$";
        };
      };

      # ★ `edges n` forces n's OWN write cell. `writersOf` indexes every writer once, n included,
      # so a direct `edges` call on a unit whose own target is ill-formed meets that unit's
      # `writesOf` refusal; the per-node scan it replaced skipped n by name and answered a value.
      # `accumulatorOrder` forces every unit's cell either way, so only this direct call moved.
      test-edges-on-a-unit-whose-own-write-cell-refuses-names-the-refusal = {
        expr =
          let
            unitAt =
              channel:
              v.unit {
                inherit (f) relation;
                target = v.placement.targets.root {
                  scope = "leaf";
                  inherit channel;
                };
                mode = "merge";
              };
            rel = v.accumulatorRelation {
              units = {
                good = unitAt "settings";
                bad = unitAt "other";
              };
            };
          in
          builtins.deepSeq (map (m: m.name) (
            rel.edges (builtins.head (builtins.filter (n: n.name == "bad") rel.nodes))
          )) true;
        expectedError = {
          type = "ThrownError";
          msg = "^gen-view\\.writesOf: the target names channel 'other' but the view relation is named 'settings'.*$";
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
        test-forged-target-channel-renders-a-lambda-at-writesOf =
          cell
            (v.writesOf {
              inherit (f) relation;
              target = {
                __element = "target";
                arm = "root";
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

    # A schedule node carrying string context is keyed by its text, so the admission check reads
    # it and names it, where the keying used to abort past `tryEval`. The value half is
    # `ci/tests/context-identifiers.nix`.
    flake.testsError.context-identifiers =
      let
        ctx = s: "${builtins.substring 0 0 (toString (builtins.toFile "3tsd3-ctx" "x"))}${s}";
        unknownLabel = expr: {
          inherit expr;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.labelOrder: 'nope' is not a label of L̂ \\(include, parent, or `\\$`\\)$";
          };
        };
        step = label: { inherit label; };
      in
      {
        test-a-schedule-node-carrying-context-reaches-the-admission-check = {
          expr = builtins.deepSeq (v.boundedWellDefinedSchedule {
            nodes = [
              (ctx "s0")
              "s1"
            ];
            declaredDependencies = graph.mkDeclaredEdges { };
            equations = { };
            admitsCycle = _: 1;
          }) true;
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.boundedWellDefinedSchedule: field 'admitsCycle' must return a bool for every node identifier; for `s0` it returned a int$";
          };
        };
        # A set with an `outPath` is not a letter, and is not coerced into one by the key.
        test-a-forged-letter-is-not-coerced-into-a-rank = {
          expr = f.order.precedes { outPath = "include"; } "parent";
          expectedError = {
            type = "ThrownError";
            msg = "^gen-view\\.labelOrder: <a set> is not a label of L̂ .*$";
          };
        };
        # Every rank read goes through `rankOf`, so a label outside L̂ is refused by name at each
        # published reader rather than aborting on the rank table.
        test-rankOf-names-an-unknown-label = unknownLabel (f.order.rankOf "nope");
        test-rankWord-names-an-unknown-label = unknownLabel (
          builtins.deepSeq (f.order.rankWord [ (step "nope") ]) true
        );
        test-pathPrecedes-names-an-unknown-label = unknownLabel (
          f.order.pathPrecedes [ (step "nope") ] [ (step "parent") ]
        );
        test-rankLess-names-an-unknown-label = unknownLabel (
          f.order.rankLess [ (step "nope") ] [ (step "parent") ]
        );
      };

    # ── A ROOT TARGET'S NAMES ARE REFUSED WHERE THE TARGET IS BUILT ──
    # `scope` and `channel` are the two names a root target carries, and every consumer of the
    # target interpolates them (`targetKey`, `writesOf`'s cell, `edgeSortKey` through `targetKey`).
    # The check sits in the constructor's refusal chain, AHEAD of the record, so a consumer that
    # forces only the tag (`elementOf`) already meets it; the WHNF cell is what separates that
    # placement from a lazy per-field check, which the deepSeq cells alone cannot see.
    #
    # ★ AND AGAIN AT EACH CONSUMER, because an element tag is a claim: a hand-built record tagged
    # `target` never passed `targets.root`, and the consumer names the same refusal from its own
    # site rather than aborting on the interpolation or answering a cell at the empty scope.
    flake.testsError.target-refusals =
      let
        fn = x: x;
        root = scope: channel: v.placement.targets.root { inherit scope channel; };
        forged = scope: channel: {
          __element = "target";
          arm = "root";
          inherit scope channel;
        };
        writes =
          target:
          v.writesOf {
            inherit (f) relation;
            inherit target;
            mode = "merge";
          };
        entryAt = target: {
          inherit target;
          path = [ ];
          source = {
            scope = "leaf";
            relation = "import";
          };
          mode = "merge";
        };
        cell = expr: msg: {
          expr = builtins.deepSeq expr true;
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };
      in
      {
        test-a-function-channel-is-refused-at-targets-root = cell (root "leaf" fn) "^gen-view\\.targets\\.root: field 'channel' is <a lambda>; .*$";
        test-an-int-channel-is-refused-at-targets-root = cell (root "leaf" 42) "^gen-view\\.targets\\.root: field 'channel' is 42; .*$";
        test-an-empty-channel-is-refused-at-targets-root = cell (root "leaf" "") "^gen-view\\.targets\\.root: field 'channel' is \"\"; .*$";
        test-a-function-scope-is-refused-at-targets-root = cell (root fn "settings") "^gen-view\\.targets\\.root: field 'scope' is <a lambda>; .*$";
        test-an-int-scope-is-refused-at-targets-root = cell (root 42 "settings") "^gen-view\\.targets\\.root: field 'scope' is 42; .*$";
        test-an-empty-scope-is-refused-at-targets-root = cell (root "" "settings") "^gen-view\\.targets\\.root: field 'scope' is \"\"; .*$";
        test-the-tag-alone-meets-the-channel-refusal = cell (root "leaf" fn).__element "^gen-view\\.targets\\.root: field 'channel' is <a lambda>; .*$";
        test-targetKey-meets-the-refusal-rather-than-an-abort = cell (v.placement.targetKey (root 42 "settings")) "^gen-view\\.targets\\.root: field 'scope' is 42; .*$";
        test-traceEntryOf-over-a-lambda-channel-contribution-meets-the-refusal = cell (v.traceEntryOf {
          contribution = {
            scope = "leaf";
            channel = fn;
            relation = "import";
            distance = 0;
            path = [ ];
          };
          placement = {
            mode = "merge";
            path = [ ];
          };
        }) "^gen-view\\.targets\\.root: field 'channel' is <a lambda>; .*$";
        test-forged-int-channel-is-refused-at-targetKey = cell (v.placement.targetKey (forged "leaf" 42)) "^gen-view\\.targetKey: field 'channel' is 42; .*$";
        test-forged-lambda-scope-is-refused-at-targetKey = cell (v.placement.targetKey (forged fn "settings")) "^gen-view\\.targetKey: field 'scope' is <a lambda>; .*$";
        test-forged-int-scope-is-refused-at-writesOf = cell (writes (forged 42 "settings")) "^gen-view\\.writesOf: field 'scope' is 42; .*$";
        test-forged-empty-scope-is-refused-at-writesOf = cell (writes (forged "" "settings")) "^gen-view\\.writesOf: field 'scope' is \"\"; .*$";
        test-forged-int-channel-is-refused-at-edgeSortKey = cell (v.edgeSortKey (entryAt (forged "leaf" 42))) "^gen-view\\.targetKey: field 'channel' is 42; .*$";
      };

    # ── FIELD REFUSALS: every constructor field is decided where the element is BUILT ──────────
    # Each cell forces its subject to WHNF and no further (`builtins.seq`), because that is what a
    # consumer holding the element does: `elementOf` reads the tag. A check that ran only when the
    # field is read passes a deep-forcing cell and fails this one, so each cell here discriminates
    # its own site: removing that site's check from `decided`, or its arm from the chain, reds it.
    flake.testsError.field-refusals =
      let
        fn = x: x;
        target = v.placement.targets.root {
          scope = "leaf";
          channel = "settings";
        };
        output = v.placement.targets.output { path = [ "p" ]; };
        sg = {
          inherit (f) carrier scopes edges;
          data = f.authored f.datums;
        };
        car = {
          inherit (f) labels relations;
          relatumLabels = f.roles;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
        };
        un = {
          inherit (f) relation;
          inherit target;
          mode = "merge";
        };
        compArgs = {
          channel = "settings";
          relation = "import";
          root = "leaf";
          direction = "outbound";
          inherit (f) admission order;
          wellFormed = f.admitAll;
          tieSet = v.tieSets.union;
          empty = [ ];
          combine = v.combines.listAppend;
          dedup = v.dedups.none;
        };
        c0 = builtins.head f.relation.contributions;
        entry = contribution: placement: v.traceEntryOf { inherit contribution placement; };
        cell = expr: msg: {
          expr = builtins.seq expr true;
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };
      in
      {
        test-a-relatum-label-name-list-is-decided-at-relatumLabels = cell (v.relatumLabels {
          names = [ 42 ];
        }) "^gen-view\\.relatumLabels: names carries a int where a string is required$";
        test-a-non-string-expression-is-refused-at-labelWellFormedness = cell (v.labelWellFormedness {
          alphabet = f.labels;
          expression = 42;
        }) "^gen-view\\.labelWellFormedness: field 'expression' is 42; .*$";
        test-the-alphabet-is-decided-at-labelWellFormedness-with-no-literals = cell (v.labelWellFormedness {
          alphabet = 42;
          expression = "_*";
        }) "^gen-view\\.labelWellFormedness: field 'alphabet' is not a edgeLabels carrier element .*$";
        test-the-data-order-is-decided-at-carrier = cell (v.carrier (
          car // { dataOrder = 42; }
        )) "^gen-view\\.carrier: field 'dataOrder' is not a dataOrder carrier element .*$";
        test-a-non-accessor-edge-is-refused-at-scopeGraph = cell (v.scopeGraph (
          sg
          // {
            edges = f.edges // {
              parent = 42;
            };
          }
        )) "^gen-view\\.scopeGraph: edges carry the label 'parent' bound to 42; .*$";
        test-the-carrier-is-decided-at-scopeGraph-with-no-data = cell (v.scopeGraph (
          sg
          // {
            carrier = 42;
            edges = { };
            data = [ ];
          }
        )) "^gen-view\\.scopeGraph: field 'carrier' is not a carrier carrier element .*$";
        test-the-scopes-are-decided-at-scopeGraph-with-no-data = cell (v.scopeGraph (
          sg
          // {
            scopes = 42;
            data = [ ];
          }
        )) "^gen-view\\.scopeGraph: scopes must be a list, not a int$";
        test-the-channel-is-decided-at-viewDefinition = cell (v.viewDefinition (
          f.definitionArgs // { channel = 42; }
        )) "^gen-view\\.viewDefinition: field 'channel' is not a dataOrder carrier element .*$";
        test-an-ordered-fold-order-element-is-decided-at-orderedFold = cell (v.tieSets.orderedFold {
          order = [ fn ];
        }) "^gen-view\\.tieSets\\.orderedFold: order carries a lambda where a string is required$";
        test-a-non-function-competition-key-is-refused-at-registry = cell (v.compositions.registry (
          compArgs // { entityOf = 42; }
        )) "^gen-view\\.compositions\\.registry: field 'entityOf' must be a function .*$";
        test-non-function-marks-are-refused-at-viewRelation = cell (f.mkRelation {
          marks = 42;
        }) "^gen-view\\.viewRelation: field 'marks' is 42; .*$";
        test-the-definition-is-decided-at-viewRelation = cell (f.mkRelation {
          definition = 42;
        }) "^gen-view\\.viewRelation: field 'definition' is not a viewDefinition carrier element .*$";
        test-the-graph-is-decided-at-viewRelation = cell (f.mkRelation {
          graph = 42;
        }) "^gen-view\\.viewRelation: field 'graph' is not a scopeGraph carrier element .*$";
        test-the-order-mark-is-decided-at-viewRelation = cell (f.mkRelation {
          orderMark = 42;
        }) "^gen-view\\.viewRelation: field 'orderMark' is not a labelOrder carrier element .*$";
        test-the-relation-is-decided-at-writesOf-on-the-output-arm = cell (v.writesOf (
          un
          // {
            relation = 42;
            target = output;
          }
        )) "^gen-view\\.writesOf: field 'relation' is not a viewRelation carrier element .*$";
        test-the-mode-is-decided-at-writesOf-on-the-output-arm = cell (v.writesOf (
          un
          // {
            mode = "sideways";
            target = output;
          }
        )) "^gen-view\\.writesOf: field 'mode' is \"sideways\", .*$";
        test-the-relation-is-decided-at-unit = cell (v.unit (
          un // { relation = 42; }
        )) "^gen-view\\.unit: field 'relation' is not a viewRelation carrier element .*$";
        test-the-target-is-decided-at-unit = cell (v.unit (
          un // { target = 42; }
        )) "^gen-view\\.unit: field 'target' is not a target carrier element .*$";
        test-the-mode-is-decided-at-unit = cell (v.unit (
          un // { mode = "sideways"; }
        )) "^gen-view\\.unit: field 'mode' is \"sideways\", .*$";
        test-a-member-is-decided-at-accumulatorRelation = cell (v.accumulatorRelation {
          units = {
            a = 42;
          };
        }) "^gen-view\\.accumulatorRelation: field 'units' is not a unit carrier element .*$";
        test-the-path-is-decided-at-orderedFoldOf-with-no-units = cell (v.orderedFoldOf {
          units = { };
          path = 42;
        }) "^gen-view\\.orderedFoldOf: path must be a list, not a int$";
        test-the-path-is-decided-at-targets-output = cell (v.placement.targets.output {
          path = 42;
        }) "^gen-view\\.targets\\.output: path must be a list, not a int$";
        test-the-mode-is-decided-at-place = cell (v.placement.place {
          mode = "sideways";
          path = [ ];
          name = "n";
          value = 1;
        }) "^gen-view\\.place: field 'mode' is \"sideways\", .*$";
        test-the-path-is-decided-at-place = cell (v.placement.place {
          mode = "merge";
          path = 42;
          name = "n";
          value = 1;
        }) "^gen-view\\.place: path must be a list, not a int$";
        test-the-name-is-decided-at-map = cell (v.transform.map {
          relation = f.relation;
          name = 42;
          f = c: c.datum;
        }) "^gen-view\\.map: field 'name' must be .*$";
        test-the-name-is-decided-at-scan = cell (v.transform.scan {
          relation = f.relation;
          name = 42;
          f = acc: _: acc;
          empty = [ ];
        }) "^gen-view\\.scan: field 'name' must be .*$";
        test-the-name-is-decided-at-over = cell (v.transform.over {
          relation = f.relation;
          name = 42;
          f = cs: cs;
        }) "^gen-view\\.over: field 'name' must be .*$";
        test-a-non-contribution-is-refused-at-traceEntryOf = cell (entry 42 f.placement) "^gen-view\\.traceEntryOf: field 'contribution' is 42; .*$";
        test-a-contribution-relation-is-decided-at-traceEntryOf = cell (entry (
          c0 // { relation = 42; }
        ) f.placement) "^gen-view\\.traceEntryOf: the contribution's relation is 42; .*$";
        test-a-contribution-distance-is-decided-at-traceEntryOf = cell (entry (
          c0 // { distance = { }; }
        ) f.placement) "^gen-view\\.traceEntryOf: the contribution's distance is <a set>; .*$";
        test-a-contribution-path-is-decided-at-traceEntryOf = cell (entry (
          c0 // { path = [ 42 ]; }
        ) f.placement) "^gen-view\\.traceEntryOf: the contribution's path must be .*$";
        test-the-target-is-decided-at-traceEntryOf = cell (entry (
          c0 // { channel = fn; }
        ) f.placement) "^gen-view\\.targets\\.root: field 'channel' is <a lambda>; .*$";
        test-a-non-placement-is-refused-at-traceEntryOf = cell (entry c0 42) "^gen-view\\.traceEntryOf: field 'placement' is 42; .*$";
        test-a-placement-mode-is-decided-at-traceEntryOf = cell (entry c0 {
          mode = "sideways";
          path = [ ];
        }) "^gen-view\\.traceEntryOf: field 'placement\\.mode' is \"sideways\", .*$";
        test-a-placement-path-is-decided-at-traceEntryOf = cell (entry c0 {
          mode = "merge";
          path = 42;
        }) "^gen-view\\.traceEntryOf: placement\\.path must be a list, not a int$";
        test-a-non-relation-is-refused-at-trace = cell (v.trace {
          relation = 42;
          placement = f.placement;
        }) "^gen-view\\.trace: field 'relation' is 42; .*$";
        test-a-non-placement-is-refused-at-trace = cell (v.trace {
          relation = f.relation;
          placement = 42;
        }) "^gen-view\\.trace: field 'placement' is 42; .*$";
        test-a-placement-mode-is-decided-at-trace = cell (v.trace {
          relation = f.relation;
          placement = {
            mode = "sideways";
            path = [ ];
          };
        }) "^gen-view\\.trace: field 'placement\\.mode' is \"sideways\", .*$";
        test-a-placement-path-is-decided-at-trace = cell (v.trace {
          relation = f.relation;
          placement = {
            mode = "merge";
            path = 42;
          };
        }) "^gen-view\\.trace: placement\\.path must be a list, not a int$";
        # The target/relation cross-check lives in `writesOf`, which a ONE-unit schedule never
        # forces, so `unit` decides it too. The control is `tryEval`-wrapped: bare, a
        # refuse-everything `unit` would throw the pinned message and pass the cell.
        test-a-target-naming-another-channel-is-decided-at-unit-in-a-one-unit-schedule =
          let
            order = u: v.accumulatorOrder { units.a = v.unit u; };
            ok = builtins.tryEval (builtins.deepSeq (order un) (order un));
          in
          assert ok.success && ok.value == [ "a" ];
          cell
            (order (
              un
              // {
                target = v.placement.targets.root {
                  scope = "leaf";
                  channel = "elsewhere";
                };
              }
            ))
            "^gen-view\\.writesOf: the target names channel 'elsewhere' but the view relation is named 'settings'; .*$";
      };

    # ── A CALLER-SUPPLIED FUNCTION'S RESULT IS REFUSED BY NAME WHERE IT IS CONSUMED (den-hoag-0gpyq) ──
    # Each cell forces what a consumer reads, and no more. A function's result exists only at
    # application, so its check lives at the application (`returned`, lib/refusal.nix); each message
    # names the function's role, the input it was applied to and the value it returned. The
    # `-aborts` cells are the RESIDUE no check on a result can see, because the application itself
    # aborts before a result exists (den-hoag-g8lo): they pin the evaluator's own error, unanchored,
    # and go red the day the behaviour changes.
    flake.testsError.function-result-refusals =
      let
        cell = expr: msg: {
          expr = builtins.deepSeq expr true;
          expectedError = {
            type = "ThrownError";
            inherit msg;
          };
        };
        residue = type: expr: msg: {
          expr = builtins.deepSeq expr true;
          expectedError = { inherit type msg; };
        };
        read = rel: {
          inherit (rel) value contributions dropped;
        };
        withDef = defArgs: f.mkRelation { definition = v.viewDefinition (f.definitionArgs // defArgs); };
        keyed =
          keyOf:
          withDef {
            channel = v.dataOrder {
              channel = "settings";
              inherit keyOf;
            };
          };
        edged =
          edges:
          f.mkRelation {
            graph = v.scopeGraph {
              inherit (f) carrier scopes;
              edges = f.edges // edges;
              data = f.authored f.datums;
            };
          };
        marked = marks: f.mkRelation { inherit marks; };
        fromLeaf = targets: id: if id == "leaf" then targets else [ ];
        refRead =
          args:
          (r.mkSelf {
            edges = [
              {
                from = "req";
                to = "prov";
              }
            ];
            decls = {
              req.provided = [ ];
              prov.provided = [ "read" ];
            };
            attributes.resolved = r.computeOf (r.referenceArgs // args);
          }).get
            "req"
            "resolved";
        revRead =
          args:
          (r.mkSelf {
            edges = [
              {
                from = "web1";
                to = "db1";
              }
            ];
            decls = {
              db1.role = "database";
              web1.tag = "w1";
            };
            attributes.needed = r.reverseComputeOf (r.reverseArgs // args);
          }).get
            "db1"
            "needed";
        over =
          fn:
          v.transform.over {
            relation = f.relation;
            name = "o";
            f = fn;
          };
        seeded =
          datum:
          f.mkRelation {
            graph = v.scopeGraph {
              inherit (f) carrier scopes edges;
              data = f.authored (
                f.datums
                // {
                  inc = [
                    {
                      relation = "import";
                      inherit datum;
                    }
                  ];
                }
              );
            };
            definition = v.compositions.registry {
              channel = "settings";
              relation = "import";
              root = "leaf";
              direction = "outbound";
              inherit (f) admission order;
              wellFormed = f.admitAll;
              tieSet = v.tieSets.union;
              empty = [ ];
              combine = v.combines.listAppend;
              dedup = v.dedups.none;
              entityOf = c: c.scope;
            };
          };
      in
      {
        # S1 — the competition key (`dataOrder.keyOf`; `registry.entityOf`/`role.roleOf` reach it)
        test-a-competition-key-that-is-not-a-string-is-named =
          cell (read (keyed (_: 42)))
            "^gen-view\\.viewRelation: channel 'settings''s competition key 'keyOf', for the contribution at scope 'inc', returned 42; a competition key is a string.*$";
        test-an-under-applied-competition-key-is-named =
          cell (read (keyed (_: _: "k")))
            "^gen-view\\.viewRelation: channel 'settings''s competition key 'keyOf', for the contribution at scope 'inc', returned <a lambda>; .*$";
        test-an-entityOf-returning-an-int-is-named =
          cell
            (read (
              f.mkRelation {
                definition = v.compositions.registry (
                  removeAttrs f.definitionArgs [
                    "channel"
                    "distance"
                  ]
                  // {
                    channel = "settings";
                    entityOf = _: 42;
                  }
                );
              }
            ))
            "^gen-view\\.viewRelation: channel 'settings''s competition key 'keyOf', for the contribution at scope 'inc', returned 42; .*$";
        test-a-competition-key-pattern-formal-aborts = residue "TypeError" (read (
          keyed ({ x }: "k")
        )) "called without required argument 'x'";

        # S2 — an edge accessor's result (scopeGraph)
        test-an-edge-accessor-returning-a-non-list-is-named =
          cell
            (read (edged {
              include = _: 42;
            }))
            "^gen-view\\.scopeGraph: the edge accessor 'include' at scope 'leaf' returned 42; each label's value is the accessor scope → \\[ scope \\]$";
        test-an-edge-target-that-is-not-a-string-is-named =
          cell
            (read (edged {
              include = fromLeaf [ 42 ];
            }))
            "^gen-view\\.scopeGraph: the edge accessor 'include' at scope 'leaf' returned the target 42, which is not a scope of this graph .*$";
        test-an-edge-target-outside-the-scopes-is-named =
          cell
            (read (edged {
              include = fromLeaf [ "nowhere" ];
            }))
            "^gen-view\\.scopeGraph: the edge accessor 'include' at scope 'leaf' returned the target \"nowhere\", which is not a scope of this graph \\(inc, leaf, mid, root\\); .*$";
        test-an-edge-accessor-pattern-formal-is-named =
          cell
            (read (edged {
              include = { x }: [ ];
            }))
            "^gen-view\\.scopeGraph: the edge accessor 'include' destructures an attrset \\(formals: x\\); .*$";
        test-an-edge-accessor-ellipsis-formal-aborts = residue "TypeError" (read (edged {
          include = { ... }: [ ];
        })) "expected a set but found a string";
        # CONTROL: the target check is L's only (`s —l→ s`). An R edge's target is a datum
        # (`s —r→ d`) and a Λ edge's a binding node; both are admitted as inert, not narrowed.
        test-control-an-R-or-Lambda-edge-target-outside-the-scopes-is-admitted = {
          expr = map (e: { inherit (e) label target; }) (
            builtins.filter (e: e.label != "parent") (
              (v.scopeGraph {
                inherit (f) carrier scopes;
                edges = f.edges // {
                  import = fromLeaf [ { x = 1; } ];
                  relatum-target = fromLeaf [ "binding" ];
                };
                data = f.authored f.datums;
              }).labeled.labeledEdges
                "leaf"
            )
          );
          expected = [
            {
              label = "import";
              target = {
                x = 1;
              };
            }
            {
              label = "include";
              target = "inc";
            }
            {
              label = "relatum-target";
              target = "binding";
            }
          ];
        };

        # S3/S4 — the marks accessor's result, and each mark's `admits` verdict (viewRelation)
        test-a-marks-result-that-is-not-a-list-is-named = cell (read (
          marked (_: 42)
        )) "^gen-view\\.viewRelation: field 'marks' at scope 'leaf' returned 42; .*$";
        test-a-mark-without-admits-is-named =
          cell (read (marked (_: [ { name = "m"; } ])))
            "^gen-view\\.viewRelation: field 'marks' at scope 'leaf' returned a mark that is <a set> \\(fields: name\\); .*$";
        test-a-mark-without-a-name-is-named =
          cell (read (marked (_: [ { admits = _: true; } ])))
            "^gen-view\\.viewRelation: field 'marks' at scope 'leaf' returned a mark that is <a set> \\(fields: admits\\); .*$";
        test-a-mark-whose-admits-is-not-callable-is-named =
          cell
            (read (
              marked (_: [
                {
                  name = "m";
                  admits = 42;
                }
              ])
            ))
            "^gen-view\\.viewRelation: field 'marks' at scope 'leaf' returned a mark whose 'admits' is 42; .*$";
        test-an-admits-verdict-that-is-not-a-bool-is-named =
          cell
            (read (
              marked (_: [
                {
                  name = "m";
                  admits = _: 42;
                }
              ])
            ))
            "^gen-view\\.viewRelation: a mark's 'admits' at scope 'leaf' for the label 'include' returned 42; it is a predicate on labels and must return a bool$";
        test-a-marks-pattern-formal-is-named = cell (read (
          marked ({ x }: [ ])
        )) "^gen-view\\.viewRelation: field 'marks' destructures an attrset \\(formals: x\\); .*$";
        test-a-marks-ellipsis-formal-aborts = residue "TypeError" (read (
          marked ({ ... }: [ ])
        )) "expected a set but found a string";
        test-an-admits-pattern-formal-is-named =
          cell
            (read (
              marked (_: [
                {
                  name = "m";
                  admits = { x }: true;
                }
              ])
            ))
            "^gen-view\\.viewRelation: field 'marks' at scope 'leaf' returned a mark whose 'admits' is <a lambda> destructuring an attrset \\(formals: x\\); .*$";
        # RESIDUE: `formalsOf` is `[ ]` for every functor, so a callable `admits` whose `__functor`
        # destructures passes the door and aborts on application to a label.
        test-an-admits-functor-pattern-formal-aborts = residue "TypeError" (read (
          marked (_: [
            {
              name = "m";
              admits = {
                __functor =
                  _:
                  {
                    y ? 1,
                  }:
                  true;
              };
            }
          ])
        )) "expected a set but found a string";
        # CONTROL: a callable `admits` that is not a lambda still applies (den-hoag-g8lo F-K).
        test-control-a-functor-admits-applies = {
          expr =
            (read (
              marked (_: [
                {
                  name = "m";
                  admits = {
                    __functor = _: _: true;
                  };
                }
              ])
            )).contributions != [ ];
          expected = true;
        };

        # S5 — WFD's verdict (relationEntries, and viewRelation through it)
        test-a-wellFormed-verdict-that-is-not-a-bool-is-named =
          cell
            (read (withDef {
              wellFormed = _: 42;
            }))
            "^gen-view\\.relationEntries: wellFormed \\(WFD\\), for the datum at scope 'inc' under relation 'import', returned 42; .*$";
        test-a-wellFormed-verdict-is-named-at-relationEntries =
          cell
            (v.relationEntries {
              graph = f.graph;
              scope = "root";
              relation = "import";
              wellFormed = _: 42;
            })
            "^gen-view\\.relationEntries: wellFormed \\(WFD\\), for the datum at scope 'root' under relation 'import', returned 42; .*$";
        test-a-wellFormed-pattern-formal-aborts = residue "TypeError" (read (withDef {
          wellFormed = { x }: true;
        })) "expected a set but found a list";

        # S9 — σ's verdict (referenceResolution, neededBy)
        test-a-sigma-verdict-that-is-not-a-bool-is-named =
          cell (refRead { wellFormed = _: 42; })
            "^gen-view\\.referenceResolution: result 'resolvedProvides': 'wellFormed' \\(σ\\) at node 'req' returned 42; .*$";
        test-a-reverse-sigma-verdict-that-is-not-a-bool-is-named = cell (revRead {
          wellFormed = _: 42;
        }) "^gen-view\\.neededBy: result 'consumers': 'wellFormed' \\(σ\\) at node 'web1' returned 42; .*$";

        # S11 — the engine's operator is a function, decided at construction
        test-a-non-function-query-operator-is-named =
          cell (v.referenceResolution (r.referenceArgs // { engine.query = 42; }))
            "^gen-view\\.referenceResolution: field 'engine' must be a query authority publishing a 'query'; .*$";
        test-a-non-function-queryReverse-operator-is-named = cell (v.neededBy
          (r.reverseArgs // { engine.queryReverse = 42; })
        ) "^gen-view\\.neededBy: field 'engine' must be a query authority publishing a 'queryReverse'; .*$";

        # S6 — the distance rule (its result is already refused by name: value-comparator-refusals)
        test-a-distance-pattern-formal-aborts = residue "TypeError" (read (withDef {
          distance = { x }: 1;
        })) "called without required argument 'x'";
        # S7 — the dedup key: any value is a key under `==`, so only the application's residue is pinned
        test-a-dedup-key-pattern-formal-aborts = residue "TypeError" (read (withDef {
          dedup = v.dedups.byKey { keyOf = { x }: 1; };
        })) "called without required argument 'x'";
        # S9/S10/S11 residue — σ, π and the engine operator all take attrsets, where a pattern formal can work
        test-a-sigma-pattern-formal-aborts = residue "TypeError" (refRead {
          wellFormed = { x }: true;
        }) "called without required argument 'x'";
        test-a-project-pattern-formal-aborts = residue "TypeError" (refRead {
          project = { x }: 1;
        }) "called without required argument 'x'";
        test-an-engine-query-pattern-formal-aborts = residue "TypeError" (refRead {
          engine.query = { x }: _: _: 1;
        }) "called without required argument 'x'";
        # S12/S13 residue — `map`'s and `scan`'s results are datums (content); only the application is pinned
        test-a-map-pattern-formal-aborts =
          residue "TypeError"
            (v.transform.map {
              relation = f.relation;
              name = "m";
              f = { x }: 1;
            }).value
            "called without required argument 'x'";
        test-a-scan-pattern-formal-aborts =
          residue "TypeError"
            (v.transform.scan {
              relation = f.relation;
              name = "s";
              empty = [ ];
              f = { x }: _: [ ];
            }).value
            "expected a set but found a list";
        test-an-admits-ellipsis-formal-aborts = residue "TypeError" (read (
          marked (_: [
            {
              name = "m";
              admits = { ... }: true;
            }
          ])
        )) "expected a set but found a string";

        # S14 — `over`'s elements, and its pattern formal (applied to a list)
        test-an-over-pattern-formal-is-named =
          cell (over ({ x }: [ ])).value
            "^gen-view\\.over: field 'f' destructures an attrset \\(formals: x\\); .*$";
        test-an-over-ellipsis-formal-aborts =
          residue "TypeError" (over ({ ... }: [ ])).value
            "expected a set but found a list";
        test-an-over-element-that-is-not-a-contribution-is-named =
          cell (over (_: [ 42 ])).value
            "^gen-view\\.over: the rewrite returned a sequence carrying 42; .*$";

        # LAZINESS — each check forces a result's SHAPE, never its CONTENT. A throw seeded in content
        # stays unforced by what a consumer reads; the paired `-forced` cell shows the seed is live.
        test-control-a-throwing-datum-is-not-forced-by-the-key-or-wellFormed-checks = {
          expr = builtins.length (seeded (throw "0gpyq seed")).contributions;
          expected = 3;
        };
        test-control-the-datum-seed-is-live = cell (seeded (throw "0gpyq seed: forced")).value "^0gpyq seed: forced$";
        test-control-a-throwing-mark-name-is-not-forced-by-the-marks-check = {
          expr =
            builtins.length
              (marked (_: [
                {
                  name = throw "0gpyq seed";
                  admits = _: true;
                }
              ])).contributions;
          expected = 1;
        };
        test-control-the-mark-name-seed-is-live =
          cell
            (marked (_: [
              {
                name = throw "0gpyq seed: forced";
                admits = _: false;
              }
            ])).withheld
            "^0gpyq seed: forced$";
        test-control-a-throwing-over-datum-is-not-forced-by-the-element-check = {
          expr =
            builtins.length
              (over (cs: cs ++ [ ((builtins.head cs) // { datum = throw "0gpyq seed"; }) ])).contributions;
          expected = 2;
        };
        test-control-the-over-datum-seed-is-live =
          cell (over (cs: cs ++ [ ((builtins.head cs) // { datum = throw "0gpyq seed: forced"; }) ])).value
            "^0gpyq seed: forced$";
      };
  };
}
