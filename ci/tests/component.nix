# THE DATA COMPONENT — and what replaces the retired arrival-mode oracle.
#
# ★★★ THIS FILE IS THE SUCCESSOR TO AN ORACLE THAT WAS RETIRED BY OWNER RULING, and the reason it
# is SHORTER than what it replaces is the whole point. The earlier revision made `data` A FUNCTION
# OF THE GRAPH — a deliberate divergence from Fig. 1 — which made WALK-DEPENDENCE SAYABLE: an
# accessor could consult the graph and re-emit, at one scope, datums it found by walking out of it.
# Having opened that hazard, the library invented a discriminator to DETECT what fell through it
# (sever the scope's out-edges, compare the two readings), and a whole suite to prove the detector
# worked. The detector was incomplete — it saw only re-emission routed through the scope's OWN
# out-edges, and at a SINK scope severing was the identity, so the check was vacuous exactly where
# a sink scope wins a competition.
#
# ★★★ THE DIVERGENCE IS WITHDRAWN. `data(G)` is a COMPONENT of the graph value, as Fig. 1 writes
# it, so NO TRAVERSAL CAN CHANGE WHICH DATUMS ARE IN THE COMPONENT OR WHERE THEY ARE FILED. ⇒
# SUBSTRATE RE-EMISSION IS INEXPRESSIBLE RATHER THAN DETECTED, so there is no discriminator, no
# arrival mode, and nothing for the retired suite to have been about. BY-CONSTRUCTION OVER REPAIR,
# applied to the construction that opened the hazard instead of to the mechanism that chased it.
#
# ★★ THE CLAIM IS SCOPED TO PRESENCE AND FILING, AND THE CELLS BELOW ARE SCOPED WITH IT. A caller
# CAN bind the graph and read it from inside a datum, because `scopeGraph` forces `scope` and
# `relation` but never `datum`. Membership and filing are closed loudly (both infinite recursion);
# a datum's VALUE is open, and that door is LAWFUL — computing a datum IS authoring it, which is
# the explicit declaration arm F asks for, and what arm F forbids is mechanical re-emission BY THE
# SUBSTRATE. Nothing here claims a datum's value is traversal-independent, because it is not.
#
# ★★ WHAT SURVIVES FROM THE RETIRED ORACLE IS ITS POSITIVE ARM — the claim that nothing was lost:
# the DECLARED form still competes, and wins where it should. That cell is below, because it is the
# half that would notice a redesign having thrown out the semantics with the mechanism.
#
# ★★ AND R17's SHAPE REQUIREMENT IS NOW MET BY THE COMPONENT SHAPE. "A contribution competes only
# if declared" needs no declaration field and no check: what competes is exactly what is IN the
# data component, and the only way a value gets there is for an author to write it there. AUTHORING
# INTO THE COMPONENT *IS* THE DECLARATION.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;

  # ── THE FIXTURE THE RETIRED ORACLE'S POSITIVE ARM USED ──
  # `child` sits below `host`. A datum authored AT `child` arrives at distance 0 and beats the
  # host's at distance 1. Under the retired design this was the arm proving the discriminator threw
  # away only the accident and not the semantics; under the component shape it is simply what
  # authoring a datum does, and it is kept because a redesign is exactly when a surviving semantics
  # is most likely to be dropped by accident.
  hostDatum = {
    relation = "import";
    datum = [ "host-assembled" ];
    scope = "host";
  };
  childDatum = hostDatum // {
    scope = "child";
  };
  twoScopes = [
    "host"
    "child"
  ];
  twoEdges = {
    parent = id: if id == "child" then [ "host" ] else [ ];
  };
  graphWith =
    data:
    v.scopeGraph {
      carrier = f.carrier;
      scopes = twoScopes;
      edges = twoEdges;
      inherit data;
    };
  relationOver =
    g:
    v.viewRelation {
      definition = f.mkDefinition { root = "child"; };
      graph = g;
      marks = f.noMarks;
    };

  # ── THE SWEEP'S MATERIAL ──
  # A complete argument set for a scope graph, with the `data` position left to the caller. Every
  # published callable is applied to it, so the question "does any export take this value into a
  # data position" is asked of the whole surface rather than of the one binding a reader thought of.
  graphArgs = {
    carrier = f.carrier;
    scopes = twoScopes;
    edges = twoEdges;
  };
  lawfulData = [ hostDatum ];
  # A MATERIALIZED WALK ANSWER — the thing that must have no route into a data position.
  walkAnswer = f.relation;
  # …and one of its contributions, which is the shape a caller would most plausibly try, since it
  # already carries a scope, a relation and a datum.
  #
  # ★★ IT IS RE-FILED AT A SCOPE THIS GRAPH ACTUALLY HAS, AND THAT MATTERS. A contribution comes
  # off the fixture graph and names a scope the two-scope graph below does not have — so probing
  # with it unaltered would be refused by the SCOPE check and the cells would read green while
  # saying nothing about the field set. Measured: with the closed field set removed, the unaltered
  # probe still passed. The re-filing leaves exactly one reason it can be refused, which is the
  # reason the claim is about.
  walkContribution = builtins.head f.relation.contributions // {
    scope = "host";
  };

  # ── THE SWEEP'S SUBJECT, AND ITS COVERAGE STATED HONESTLY ──
  # The published CONSTRUCTORS: callables that take a closed field set and can return a tagged
  # construction. Built from `attrNames` minus a named exclusion, so a new constructor joins the
  # sweep without anyone remembering to add it.
  #
  # ★ THE EXCLUSION IS NAMED, REASONED AND CONTROLLED RATHER THAN QUIET, and it is the ONLY hand-
  # written list here. The excluded names are BARE-RECORD HELPERS — they read fields off a record
  # positionally instead of through a closed field set, so handing them a graph's argument set
  # raises an uncatchable missing-attribute error rather than a refusal (`builtins.tryEval` catches
  # thrown errors and NOT evaluation errors — measured on this evaluator). They are excluded because
  # a probe cannot survive them, NOT because they were inconvenient, and the cell below shows each
  # one constructs nothing at all, which is why their exclusion costs the claim nothing. The
  # PARTITION is asserted total, so a name can be neither swept nor excluded only by taking a cell
  # red.
  bareRecordHelpers = [
    "cell"
    "edgeSortKey"
    "renderEntry"
    "renderTrace"
    "placement.pathKey"
    "placement.sourceKey"
    "placement.targetKey"
  ];
  # ★★★ THE ROSTER IS DERIVED BY WALKING THE PUBLISHED SURFACE, NOT BY NAMING FAMILIES. An earlier
  # revision enumerated four families by hand — `placement`, `placement.targets`, `transform`,
  # `compositions` — and that left FIVE reachable callables in NEITHER partition:
  # `combines.setUnion`, `combines.listAppend.op`, `combines.attrsShallow.op`, `dedups.byKey` and
  # `tieSets.orderedFold`, because `combines`, `dedups` and `tieSets` are attrset exports whose
  # callables were never enumerated. The absence claim survived — none of the five yields a graph —
  # but the COVERAGE SENTENCE described a hand-written list rather than the surface, and a
  # constructor added inside those families would have joined neither the sweep nor the exclusion
  # note SILENTLY. A derived roster does not drift that way: a new export joins the walk by existing
  # — ★ SO LONG AS IT IS WITHIN THE WALK'S REACH, which is why the partition cell carries a
  # FIXED-POINT ARM and not a depth bound alone. The bound is exactly saturated by the real surface
  # today, so unqualified that sentence would be true only up to a depth the surface has reached.
  #
  # The walk descends through attrset-valued exports to the depth the surface actually nests (a
  # combine RECORD holds its `op`, which is two levels below the top), and skips the `__element`
  # tags, which are strings and not part of the callable surface.
  walkSurface =
    depth: prefix: val:
    if builtins.isFunction val then
      [
        {
          name = prefix;
          value = val;
        }
      ]
    else if builtins.isAttrs val && depth > 0 then
      builtins.concatMap (
        n: walkSurface (depth - 1) (if prefix == "" then n else "${prefix}.${n}") val.${n}
      ) (builtins.filter (n: n != "__element") (builtins.attrNames val))
    else
      [ ];
  walkDepth = 3;
  allCallables = walkSurface walkDepth "" v;
  # ★★★ THE SAME WALK AT A DEPTH NOTHING ON THIS SURFACE COULD SATURATE. Read only by the
  # fixed-point arm below: if the two walks disagree, the shallow one is missing something and every
  # count taken from it is a count of the wrong set.
  deeperCallables = walkSurface (walkDepth + 5) "" v;
  constructors = builtins.filter (c: !(builtins.elem c.name bareRecordHelpers)) allCallables;

  # `yieldsGraph` — the predicate. Not "does it evaluate" (a partially-applied function evaluates
  # to a function and would read as acceptance) but "does it PRODUCE A SCOPE GRAPH", which is the
  # actual question: is there a published route from this value to a graph holding it as data.
  yieldsGraph =
    dataValue: c:
    let
      probe = builtins.tryEval (
        let
          out = c.value (graphArgs // { data = dataValue; });
        in
        builtins.isAttrs out && (out.__element or null) == "scopeGraph"
      );
    in
    probe.success && probe.value;

  routesFor = dataValue: map (c: c.name) (builtins.filter (yieldsGraph dataValue) constructors);

  # ── THE SOURCE ANGLE, which is TOTAL where the apply-sweep is not ──
  # A scope graph is a TAGGED construction, so counting the sites that EMIT the tag counts the
  # constructions that can make one — no application, no probe, nothing to raise. The needle is the
  # emission form `__element = "scopeGraph"`, which cannot occur in prose the way the bare word can.
  libFiles = builtins.filter (n: builtins.match ".*\\.nix" n != null) (
    builtins.attrNames (builtins.readDir ../../lib)
  );
  occurrences =
    needle: text: builtins.length (builtins.filter (x: builtins.isList x) (builtins.split needle text));
  countAcrossLib =
    needle:
    builtins.foldl' (
      acc: n: acc + occurrences needle (builtins.readFile (../../lib + "/${n}"))
    ) 0 libFiles;

in
{
  flake.tests.component = {
    # ══ THE ABSENCE: NO EXPORTED NAME TAKES A WALK ANSWER INTO A DATA POSITION ══
    #
    # ★★★ AND ITS FIRING CONTROL IS IN THE SAME CELL, ON THE SAME PREDICATE, OVER THE SAME SURFACE.
    # An empty list is a claim that a sweep found nothing; without a control it is equally
    # consistent with a sweep that COULD find nothing — a predicate that never matches, an empty
    # callable list, a probe that swallows its own errors. Handed LAWFUL data the same sweep must
    # return exactly `scopeGraph`, and nothing else, because `scopeGraph` is the only construction
    # that holds a data component at all.
    test-no-export-carries-a-walk-answer-into-a-data-position = {
      expr = {
        aMaterializedResult = routesFor walkAnswer;
        aContributionFromOne = routesFor [ walkContribution ];
        control = routesFor lawfulData;
      };
      expected = {
        aMaterializedResult = [ ];
        aContributionFromOne = [ ];
        control = [ "scopeGraph" ];
      };
    };

    # ★★★ THE PARTITION IS TOTAL OVER THE REACHABLE SURFACE, AND THAT IS THE CLAIM — not a count.
    # Every callable reachable on the published surface is either SWEPT or EXCLUDED-AND-CONTROLLED,
    # with nothing in between. An earlier revision pinned a number about a hand-enumerated set, which
    # is a coverage sentence that can be true while five reachable callables sit outside both
    # partitions; this asserts the property that number was standing in for.
    test-control-the-sweep-partitions-the-whole-reachable-surface = {
      expr = {
        # nothing reachable falls outside the two partitions
        inNeither = builtins.filter (
          c: !(builtins.elem c.name bareRecordHelpers) && !(builtins.elem c constructors)
        ) allCallables;
        partitionIsTotal =
          builtins.length constructors + builtins.length bareRecordHelpers == builtins.length allCallables;
        # …and the surface it partitions is a real one, stated as a bound so a new export does not
        # take this red for existing
        reachable = builtins.length allCallables > 40;
        excluded = builtins.length bareRecordHelpers;
        # ★★★ THE FIXED-POINT ARM, AND WITHOUT IT EVERY OTHER FIELD IN THIS CELL IS
        # SELF-REFERENTIAL. `inNeither`, `partitionIsTotal` and `reachable` are all computed from
        # `allCallables` — the SUBJECT and the YARDSTICK are the same walk — so a callable the walk
        # MISSES is absent from both, and all three stay green while it sits outside the roster.
        # Measured: the real surface nests EXACTLY to the bound, zero headroom, and a seeded
        # depth-4 export is invisible to `walk 3`, visible to `walk 4`, and leaves `inNeither = [ ]`,
        # `partitionIsTotal = true` and `reachable = true` untouched.
        #
        # Comparing the walk against a DEEPER walk breaks the self-reference, because the yardstick
        # is no longer the subject. Anything nested past the bound makes the two disagree and takes
        # this cell red — a roster can only be trusted complete by something that is not the roster.
        # ★ COMPARED BY NAME, AND THAT IS NOT A WEAKENING — IT IS THE LANGUAGE. These are records
        # holding FUNCTIONS, and two Nix lambdas are never equal, not even against themselves, so a
        # record-wise comparison reads `false` on a walk that is a perfect fixed point. Measured
        # here, on this cell, before it was corrected. The names are the roster's identity anyway:
        # what the arm asks is whether the deeper walk REACHES ANYTHING THE SHALLOW ONE DID NOT.
        walkIsAFixedPoint = map (c: c.name) allCallables == map (c: c.name) deeperCallables;
      };
      expected = {
        inNeither = [ ];
        partitionIsTotal = true;
        reachable = true;
        # 8 until `placement.setAttrByPath` retired to gen-prelude (2026-08-27 ruling).
        excluded = 7;
        walkIsAFixedPoint = true;
      };
    };

    # ★★ AND THE FIVE THAT USED TO SIT OUTSIDE BOTH PARTITIONS ARE NAMED, so the regression has a
    # subject. They are SWEPT now — each takes a closed field set or is a curried operator, so a
    # probe survives all five — and the cell fails if any drops back out of the walk.
    test-control-the-previously-unswept-family-members-are-now-swept = {
      expr = builtins.filter (n: builtins.elem n (map (c: c.name) constructors)) [
        "combines.setUnion"
        "combines.listAppend.op"
        "combines.attrsShallow.op"
        "dedups.byKey"
        "tieSets.orderedFold"
      ];
      expected = [
        "combines.setUnion"
        "combines.listAppend.op"
        "combines.attrsShallow.op"
        "dedups.byKey"
        "tieSets.orderedFold"
      ];
    };

    # ══ THE ROUTE IS CLOSED AT THE CONSTRUCTOR, BY NAME AND FOR A STATED REASON ══
    # The sweep says no export does it; these say why nothing can. A datum is exactly three fields,
    # and a contribution carries its path, its residual admission state, its distance and its
    # channel besides — so it is refused in a data position rather than quietly carried into
    # competition.
    test-a-walk-answer-is-refused-in-a-data-position-by-name = {
      expr = {
        aContribution = refuses (graphWith [ walkContribution ]);
        aMaterializedResult = refuses (graphWith walkAnswer);
        # ★ AND THE ONE THAT MATTERS MOST: `data` MAY NOT BE A FUNCTION. A function of the graph is
        # exactly the divergence the owner withdrew — it is what made walk-dependence sayable, and
        # accepting one here would reopen the hazard no matter what else this file asserts.
        aFunctionOfTheGraph = refuses (graphWith (_: _: [ hostDatum ]));
        anAccessor = refuses (graphWith (_: [ hostDatum ]));
      };
      expected = {
        aContribution = true;
        aMaterializedResult = true;
        aFunctionOfTheGraph = true;
        anAccessor = true;
      };
    };

    # ★ THE CONTROL: the lawful component constructs, and STRIPPING a contribution back to the
    # three fields is what authoring one looks like. Nothing is unreachable — a person can write
    # down anything a walk found; what they cannot do is have the walk write it for them.
    test-control-a-lawful-component-constructs-and-a-stripped-contribution-is-authorable = {
      expr = {
        lawful = (graphWith lawfulData).__element;
        stripped =
          (graphWith [
            {
              inherit (walkContribution) scope relation datum;
            }
          ]).__element;
      };
      expected = {
        lawful = "scopeGraph";
        stripped = "scopeGraph";
      };
    };

    # ══ (NR-Rel) TAKES NO GRAPH-TO-READ-AGAINST, AND THE ABSENT PARAMETER IS THE POINT ══
    # The retired signature carried a `labeled` argument, so a caller could pass a modified graph
    # and get a different answer at the same scope — two readings of one component, which is the
    # walk-dependence the component shape removes. A membership test against a value has no such
    # parameter. Pinned on the FORMALS, because that is where the property lives.
    test-the-relation-lookup-takes-exactly-four-fields = {
      expr =
        let
          complete = {
            graph = f.graph;
            scope = "inc";
            relation = "import";
            wellFormed = f.admitAll;
          };
        in
        {
          # each of the four is REQUIRED — omit one and the rule refuses
          omissions = map (n: refuses (v.relationLookup (removeAttrs complete [ n ]))) (
            builtins.attrNames complete
          );
          # …and the complete four answer
          complete = v.relationLookup complete;
        };
      expected = {
        omissions = [
          true
          true
          true
          true
        ];
        complete = [ [ "inc" ] ];
      };
    };

    test-the-relation-lookup-refuses-an-argument-it-no-longer-takes = {
      expr = refuses (
        v.relationLookup {
          graph = f.graph;
          labeled = f.graph.labeled;
          scope = "inc";
          relation = "import";
          wellFormed = f.admitAll;
        }
      );
      expected = true;
    };

    # ══ THE SURVIVOR OF THE RETIRED ORACLE'S POSITIVE ARM ══
    # ★★ NOTHING WAS LOST WITH THE MECHANISM. A datum AUTHORED at `child` competes, and wins on its
    # empty path against the host's at distance 1. Under the retired design this arm proved the
    # discriminator threw away only the accident; it is kept because a redesign is exactly when a
    # surviving semantics is most likely to go out with the machinery.
    test-the-declared-form-competes-and-wins-where-it-should = {
      expr =
        let
          r = relationOver (graphWith [
            hostDatum
            childDatum
          ]);
        in
        {
          visible = map (c: {
            inherit (c) scope distance;
          }) r.contributions;
          shadowed = map (c: c.scope) r.shadowed;
          value = r.value;
        };
      expected = {
        visible = [
          {
            scope = "child";
            distance = 0;
          }
        ];
        shadowed = [ "host" ];
        value = [ "host-assembled" ];
      };
    };

    # ★ THE CONTROL: WITHOUT the child's authored datum the host's is what wins. So the cell above
    # measures the authored datum competing, not a fixture that answers the same way either way.
    test-control-without-the-authored-datum-the-host-wins = {
      expr =
        let
          r = relationOver (graphWith [ hostDatum ]);
        in
        {
          visible = map (c: {
            inherit (c) scope distance;
          }) r.contributions;
          value = r.value;
        };
      expected = {
        visible = [
          {
            scope = "host";
            distance = 1;
          }
        ];
        value = [ "host-assembled" ];
      };
    };

    # ══ THE COMPONENT IS A VALUE, AND ITS SHAPE IS Fig. 1's ══
    # `Data ::= s —r→ d`. A datum filed at a scope the graph does not have, or under a relation the
    # carrier does not declare, is refused: the component is part of the graph, so it may not name
    # things the graph has never heard of.
    test-the-component-is-fig-1s-triple-and-is-checked-against-the-graph = {
      expr = {
        shape = builtins.sort builtins.lessThan (builtins.attrNames (builtins.head f.graph.data));
        offScope = refuses (graphWith [ (hostDatum // { scope = "nowhere"; }) ]);
        offRelation = refuses (graphWith [ (hostDatum // { relation = "not-declared"; }) ]);
      };
      expected = {
        shape = [
          "datum"
          "relation"
          "scope"
        ];
        offScope = true;
        offRelation = true;
      };
    };

    # ══ THE SOURCE ANGLE: EXACTLY ONE CONSTRUCTION IN THE LIBRARY EMITS A SCOPE GRAPH ══
    #
    # ★★★ THIS IS WHAT MAKES THE ABSENCE TOTAL. The apply-sweep above covers the constructors and
    # says none of them takes a walk answer into a data position; this says there is only ONE
    # construction that produces a graph at all, so "the one constructor refuses it" IS "no route
    # exists". Together: one door, and it is shut against a walk answer.
    test-exactly-one-construction-emits-a-scope-graph = {
      expr = countAcrossLib "__element = \"scopeGraph\"";
      expected = 1;
    };

    # ★ THE FIRING CONTROL, same instrument, same run, same corpus: the counter finds the OTHER
    # tagged constructions, so a count of one is a measurement and not a predicate that matches
    # nothing. Stated as a bound so a new element does not take this red for existing.
    test-control-the-tag-counter-finds-the-other-constructions = {
      expr = countAcrossLib "__element = " > 8;
      expected = true;
    };

    # ★★ THE EXCLUSION FROM THE APPLY-SWEEP COSTS THE CLAIM NOTHING, MEASURED RATHER THAN ASSERTED.
    # Each excluded name is a bare-record helper: applied to its OWN proper argument it returns a
    # string, a list or a plain attrset carrying no `__element` at all. A callable that constructs
    # nothing cannot construct a graph, so leaving it out of a sweep about graph construction
    # removes no coverage.
    test-control-every-excluded-helper-constructs-nothing = {
      expr = {
        excluded = bareRecordHelpers;
        tags = [
          ((v.cell "s" "c" "input").__element or null)
          ((v.edgeSortKey (
            v.traceEntryOf {
              contribution = walkContribution;
              placement = f.placement;
            }
          )).__element or null
          )
          ((v.renderEntry (
            v.traceEntryOf {
              contribution = walkContribution;
              placement = f.placement;
            }
          )).__element or null
          )
          ((v.renderTrace [ ]).__element or null)
          ((v.placement.pathKey [ "a" ]).__element or null)
          ((v.placement.sourceKey {
            scope = "s";
            relation = "r";
          }).__element or null
          )
          ((v.placement.targetKey (v.placement.targets.output { path = [ "p" ]; })).__element or null)
        ];
      };
      expected = {
        excluded = [
          "cell"
          "edgeSortKey"
          "renderEntry"
          "renderTrace"
          "placement.pathKey"
          "placement.sourceKey"
          "placement.targetKey"
        ];
        tags = [
          null
          null
          null
          null
          null
          null
          null
        ];
      };
    };

    # ══ THE SCOPED CLAIM, PINNED — A COMPUTED DATUM IS LAWFUL AND MUST STAY LAWFUL ══
    #
    # ★★★ THIS CELL EXISTS TO STOP A FUTURE READER "FIXING" A DOOR THAT IS MEANT TO BE OPEN. The
    # library once claimed WALK-DEPENDENCE IS UNSAYABLE without qualification, and that claim was
    # false: `scopeGraph` forces `scope` and `relation` but never `datum`, and `labeled` is
    # computable from `edges` and `scopes` without `data` — so a caller can bind the graph and read
    # it from inside a datum. Someone meeting the old sentence and this fact would reasonably try to
    # close the door. THEY MUST NOT: a datum's VALUE is the author's and is not analysed, computing
    # one IS authoring it, and that is exactly ADR-0024 arm F's *declared explicitly rather than as
    # an implicit side effect*. What arm F forbids is MECHANICAL RE-EMISSION BY THE SUBSTRATE, which
    # is gone — the library performs one gather and consults no accessor.
    #
    # ★★ THE OTHER TWO DOORS CANNOT BE CELLS, AND THAT IS STATED RATHER THAN QUIETLY OMITTED.
    # Making a datum's MEMBERSHIP or its FILING SCOPE a function of the graph is INFINITE RECURSION
    # — `scopeGraph` forces both to validate them, so the knot ties itself. Infinite recursion is
    # not catchable by `builtins.tryEval` on this evaluator, so a cell asserting those doors are
    # closed would take the whole suite down rather than pass. They are verified by hand, one
    # evaluation each, and recorded here as measured-not-celled.
    test-a-computed-datum-is-lawful-and-participates = {
      expr =
        let
          # `inc` is reachable from `leaf` by `include` in BOTH graphs, so the counterfactual varies
          # an edge that does NOT decide whether the datum's scope is reached — only its VALUE.
          mk =
            midHasParent:
            let
              g = v.scopeGraph {
                carrier = f.carrier;
                scopes = f.scopes;
                edges = {
                  parent =
                    id:
                    if id == "leaf" then
                      [ "mid" ]
                    else if id == "mid" && midHasParent then
                      [ "root" ]
                    else
                      [ ];
                  include = id: if id == "leaf" then [ "inc" ] else [ ];
                };
                data = [
                  {
                    scope = "inc";
                    relation = "import";
                    datum = if (g.labeled.labeledEdges "mid") != [ ] then [ "admit" ] else [ "reject" ];
                  }
                ];
              };
            in
            v.viewRelation {
              definition = f.mkDefinition { wellFormed = d: d == [ "admit" ]; };
              graph = g;
              marks = f.noMarks;
            };
          withEdge = mk true;
          without = mk false;
        in
        {
          # it BUILDS and MATERIALIZES — the door is open
          builds = withEdge.value;
          # …and participation follows graph shape, which is the honest form of the claim
          withParentEdge = map (c: c.scope) withEdge.contributions;
          withoutParentEdge = map (c: c.scope) without.contributions;
          valueWithout = without.value;
        };
      expected = {
        builds = [ "admit" ];
        withParentEdge = [ "inc" ];
        withoutParentEdge = [ ];
        valueWithout = [ ];
      };
    };

    # ★ THE CONTROL THAT THE COUNTERFACTUAL IS REACHABILITY-NEUTRAL: the datum's scope is reached in
    # BOTH graphs, so the participation difference above is about the datum's VALUE and not about
    # whether the walk got there. Without this the cell is consistent with an edge that simply cut
    # the scope off.
    test-control-the-counterfactuals-scope-is-reached-in-both-graphs = {
      expr =
        let
          reached =
            midHasParent:
            map (c: c.scope)
              (v.viewRelation {
                definition = f.mkDefinition { };
                graph = v.scopeGraph {
                  carrier = f.carrier;
                  scopes = f.scopes;
                  edges = {
                    parent =
                      id:
                      if id == "leaf" then
                        [ "mid" ]
                      else if id == "mid" && midHasParent then
                        [ "root" ]
                      else
                        [ ];
                    include = id: if id == "leaf" then [ "inc" ] else [ ];
                  };
                  data = [
                    {
                      scope = "inc";
                      relation = "import";
                      datum = [ "plain" ];
                    }
                  ];
                };
                marks = f.noMarks;
              }).contributions;
        in
        {
          withParentEdge = reached true;
          withoutParentEdge = reached false;
        };
      expected = {
        withParentEdge = [ "inc" ];
        withoutParentEdge = [ "inc" ];
      };
    };
  };
}
