# THE REFERENCE-RESOLUTION FIXTURE — one construction of the REAL query authority, reached by
# every cell that has anything to say about `referenceResolution` or about its reverse half
# `neededBy`. ★ ONE authority for BOTH directions, deliberately: the two operators live on the same
# injected value, so a second fixture would make each direction's values a claim about its own
# evaluator rather than about the delegate the two constructs share.
#
# It lives OUTSIDE `./tests` for the same reason `fixture.nix` does: `testModules` is the whole of
# `flake.tests`, so a plain value module in that tree would be read as a suite and contribute cells
# of its own. It is a second file rather than an extension of `fixture.nix` because that one is a
# function of the library under test AND NOTHING ELSE, and this one needs the injected authority —
# widening its formals would make every suite that imports it carry a dependency only these cells
# have.
#
# ★★ THE AUTHORITY IS REAL, AND THE ORACLES ARE WHY. A hand-written engine would turn the
# delegation cell and the multi-candidate cell into assertions about the fixture: the first has to
# show the REAL authority answering where a stub's sentinel comes back, and the second asserts the
# disposal the real delegate performs on a candidate set nothing in the calculus orders. Neither
# claim survives a mimic. This is a `ci/` dependency on the same terms as nixpkgs — the library
# takes its authority as an INJECTED FIELD and reaches no evaluator, which
# `ci/tests/reference.nix` asserts over `../lib`'s own source rather than leaving to this comment.
#
# ★ THE IMPORT EDGES ARE DECLARED ONCE AND READ TWICE, from one list. The authority needs them as a
# GRAPH (to build the node set) and the evaluator needs them as an `imports` ATTRIBUTE (to walk),
# and a fixture that wrote the two by hand would have two declarations of one relation with nothing
# comparing them — the drift class this ecosystem has measured twice. The consumer builds its own
# index the same way, by folding the merged graph's edges.
{ genView, genScope }:
let
  v = genView;
  s = genScope;

  # `mkSelf { edges; decls; attributes; }` — an evaluator over a declared import graph. `children`
  # and `imports` are the structural attributes every scope needs; `attributes` carries the
  # computes under test.
  mkSelf =
    {
      edges,
      decls,
      attributes,
    }:
    let
      importIndex = builtins.foldl' (
        acc: e: acc // { ${e.from} = (acc.${e.from} or [ ]) ++ [ e.to ]; }
      ) { } edges;
    in
    s.eval {
      scope = s.buildRoots {
        importGraph = s.overlays (map (e: s.edge e.from e.to) edges);
        inherit decls;
      };
      attributes = {
        children = _self: _id: { };
        imports = _self: id: importIndex.${id} or [ ];
      }
      // attributes;
      parseParent = _id: null;
    };

  computeOf = args: (v.referenceResolution args).compute;

  # ── THE CONSUMER'S OWN SHAPE ──
  # `req` includes `prov`; the provider carries capability tags and the requirer carries none, so
  # the local candidate is not a binding and resolution walks the include edge. This is the live
  # call site's declaration verbatim — a list-valued projection over `decls.provided` — which is
  # what makes the refusal sweep's positive control a statement about the shape that ships rather
  # than about a shape invented for it.
  providesEdges = [
    {
      from = "req";
      to = "prov";
    }
  ];
  providesDecls = {
    req = {
      provided = [ ];
    };
    prov = {
      provided = [
        "read"
        "write"
      ];
    };
  };

  # THE COMPLETE DECLARATION. The refusal sweep removes one field at a time from this, so "each
  # omitted field refuses by name" quantifies over the library's own published enumeration rather
  # than over a list somebody typed twice.
  referenceArgs = {
    engine = s;
    name = "resolvedProvides";
    wellFormed = n: (n.decls.provided or [ ]) != [ ];
    project = n: n.decls.provided;
    localShadowsImport = true;
    importShadowsParent = true;
    transitiveImports = false;
  };

  # THE STUB AUTHORITY — a `query` that ignores its arguments entirely and answers a sentinel. It
  # is the whole of the delegation oracle: a construct that computed any part of the answer itself
  # could not return this.
  sentinel = "the-stub-authority-answered";
  stubEngine = {
    query =
      _args: _self: _id:
      sentinel;
  };

  providesSelf = mkSelf {
    edges = providesEdges;
    decls = providesDecls;
    attributes = {
      # The real authority and the stub, over ONE declaration in ONE evaluator, so the two arms
      # differ in exactly the injected field and in nothing else.
      resolved = computeOf referenceArgs;
      stubbed = computeOf (referenceArgs // { engine = stubEngine; });
    };
  };

  # ── THE NULL PROJECTION, AND THE ORDINARY ABSENCE BESIDE IT ──
  # `reader` includes `holder`, which IS well-formed; `lonely` includes `blank`, which is NOT. The
  # second pair is what keeps the refusal bounded: a node no predicate admits is an ordinary
  # absence and must stay one, so the guard must not fire there.
  projectionEdges = [
    {
      from = "reader";
      to = "holder";
    }
    {
      from = "lonely";
      to = "blank";
    }
  ];
  projectionDecls = {
    reader = { };
    holder = {
      tag = "present";
    };
    lonely = { };
    blank = { };
  };

  admitsTag = n: n.decls ? tag;
  nullProject = _n: null;
  tagProject = n: n.decls.tag;
  projectionArgs = referenceArgs // {
    name = "tagOfNearestHolder";
    wellFormed = admitsTag;
  };

  # ★ THE CONSTRUCT'S COMPOSED FILTER WITH THE GUARD REMOVED AND NOTHING ELSE CHANGED — π ∘ σ, the
  # two operators composed the way the construct composes them, minus `requireNonNull`. Written as
  # one binding rather than inline at each arm so that the guarded and unguarded readings differ in
  # EXACTLY the guard: two hand-written near-copies would let the comparison drift into measuring
  # the copies.
  unguarded =
    {
      wellFormed,
      project,
    }:
    n: if wellFormed n then project n else null;

  unguardedQuery =
    args:
    s.query {
      dataFilter = unguarded args;
      localShadowsImport = true;
      importShadowsParent = true;
      transitiveImports = false;
    };

  projectionSelf = mkSelf {
    edges = projectionEdges;
    decls = projectionDecls;
    attributes = {
      # The subject: a node the predicate ADMITS whose projection is null.
      nullArm = computeOf (projectionArgs // { project = nullProject; });
      # The positive arm: the same fixture and the same declaration with a non-null projection.
      tagArm = computeOf (projectionArgs // { project = tagProject; });
      # ★ THE VACUITY ARM — the same composition with the guard removed. On its own a null here
      # would be worth nothing, because an unreached node answers null too.
      unguardedNullArm = unguardedQuery {
        wellFormed = admitsTag;
        project = nullProject;
      };
      # ★ WHICH IS WHAT THIS ONE IS FOR: the SAME unguarded composition at a non-null projection
      # must answer the holder's datum. It is the reachability control for the arm above — with it,
      # the null there is the PROJECTION's null and not a node the walk never reached.
      unguardedTagArm = unguardedQuery {
        wellFormed = admitsTag;
        project = tagProject;
      };
    };
  };

  # ── THE MULTI-CANDIDATE FIXTURE ──
  # `r` includes BOTH `A` and `B`, both admitted, so the candidate set the delegate must dispose is
  # non-singleton — the case nothing in the specificity ordering decides. `q` includes EXACTLY ONE
  # admitted node, which is the control: it exercises the same IMPORT PATH and answers one node's
  # own datum, so a subject value below cannot be an artefact of a fixture that resolved nothing.
  # (A control node with NO imports would answer its own LOCAL datum and never enter the import
  # path at all, which is a different claim and a weaker one.)
  multiEdges = [
    {
      from = "r";
      to = "A";
    }
    {
      from = "r";
      to = "B";
    }
    {
      from = "q";
      to = "A";
    }
  ];
  multiDecls = {
    r = { };
    q = { };
    A = {
      d = {
        a = 1;
      };
      l = [ "a" ];
    };
    B = {
      d = {
        b = 2;
      };
      l = [ "b" ];
    };
  };

  multiArgs = field: {
    engine = s;
    name = "candidate-${field}";
    wellFormed = n: n.decls ? ${field};
    project = n: n.decls.${field};
    localShadowsImport = true;
    importShadowsParent = true;
    transitiveImports = false;
  };

  multiSelf = mkSelf {
    edges = multiEdges;
    decls = multiDecls;
    attributes = {
      # ARM (i) — an ATTRSET-valued projection.
      attrsArm = computeOf (multiArgs "d");
      # ARM (ii) — a LIST-valued projection, which is the live consumer's type.
      listArm = computeOf (multiArgs "l");
    };
  };

  # ══ THE REVERSE HALF — `neededBy` OVER THE SAME EVALUATOR AND THE SAME REAL AUTHORITY ═══════
  #
  # ★ IT REUSES `mkSelf`, WHICH IS THE POINT. The reverse operator lives on the same injected
  # authority as the forward one, so building it against a second evaluator would make every value
  # below a claim about a fixture rather than about the delegate. One `mkSelf`, two directions.

  reverseComputeOf = args: (v.neededBy args).compute;

  # ── THE GATHER FIXTURE ──
  # `web1`, `web2` and `mid` all import `db1`, so `db1` has THREE reverse contributors — the shape
  # the forward arm cannot have, where the delegate refuses a candidate set it cannot order. `web1`
  # ALSO imports `mid`, which gives `db1` a SECOND reverse path to `web1` and is what makes the
  # transitive arm's duplicate contribution observable. `db1` carries a datum of its own that no
  # predicate here admits, so nothing in its answer can be its own.
  gatherEdges = [
    {
      from = "web1";
      to = "db1";
    }
    {
      from = "web2";
      to = "db1";
    }
    {
      from = "web1";
      to = "mid";
    }
    {
      from = "mid";
      to = "db1";
    }
  ];
  gatherDecls = {
    db1 = {
      role = "database";
    };
    web1 = {
      tag = "w1";
    };
    web2 = {
      tag = "w2";
    };
    mid = {
      tag = "m";
    };
  };

  admitsTagged = n: n.decls ? tag;
  tagOf = n: n.decls.tag;

  reverseArgs = {
    engine = s;
    name = "consumers";
    wellFormed = admitsTagged;
    project = tagOf;
    transitive = false;
  };

  # THE REVERSE STUB AUTHORITY — a `queryReverse` ignoring its arguments entirely, answering a
  # sentinel. It is the whole of the reverse delegation oracle, on the forward stub's own terms.
  # ★ IT PUBLISHES NO `query`, and `stubEngine` above publishes no `queryReverse`: the two stubs
  # are each other's wrong-authority arm, so "the engine check names the operator THIS construct
  # needs" is checked in both directions rather than asserted in one.
  reverseSentinel = "the-reverse-stub-authority-answered";
  reverseStubEngine = {
    queryReverse =
      _args: _self: _id:
      reverseSentinel;
  };

  gatherSelf = mkSelf {
    edges = gatherEdges;
    decls = gatherDecls;
    attributes = {
      # The two `transitive` arms over ONE declaration in ONE evaluator, differing in exactly the
      # declared field — a construct that ignored it answers the same value twice.
      direct = reverseComputeOf reverseArgs;
      transitive = reverseComputeOf (reverseArgs // { transitive = true; });
      # The real authority and the reverse stub, likewise differing in exactly the injected field.
      stubbed = reverseComputeOf (reverseArgs // { engine = reverseStubEngine; });
      # ★ THE CONTRIBUTOR'S IDENTITY beside its datum, over the same fixture: a different π, a
      # different answer, which is what makes the datum arm a statement about `project` and not
      # about a walk that reached one node.
      identities = reverseComputeOf (reverseArgs // { project = n: n.id; });
    };
  };

  # ── THE REVERSE NULL PROJECTION ──
  # `nullnode` imports `db1` and IS admitted by the predicate, and its projection is null. Beside
  # it `web1` imports `db1` and projects a datum, so the gather is non-empty either way — which is
  # exactly why the defect is invisible without the guard: the admitted contributor VANISHES from a
  # list that still has something in it.
  reverseNullEdges = [
    {
      from = "web1";
      to = "db1";
    }
    {
      from = "nullnode";
      to = "db1";
    }
  ];
  mkReverseNullSelf =
    nullnodeTag:
    mkSelf {
      edges = reverseNullEdges;
      decls = {
        db1 = {
          role = "database";
        };
        web1 = {
          tag = "w1";
        };
        nullnode = {
          tag = nullnodeTag;
        };
      };
      attributes = {
        gathered = reverseComputeOf reverseArgs;
        # ★ THE VACUITY ARM — the same π ∘ σ composition with the guard removed and nothing else
        # changed, reached through the delegate directly. Written from the shared `unguarded`
        # binding above so the guarded and unguarded readings differ in EXACTLY the guard.
        unguarded = s.queryReverse {
          dataFilter = unguarded {
            wellFormed = admitsTagged;
            project = tagOf;
          };
        };
      };
    };

  # The subject: the admitted contributor projects null.
  reverseNullSelf = mkReverseNullSelf null;
  # ★ THE CONTROL, same fixture and same declaration, differing ONLY in that one datum. It is what
  # shows the fixture genuinely builds the subject: the node is reached, admitted and projected.
  reverseNonNullSelf = mkReverseNullSelf "NN";
in
{
  inherit
    v
    s
    mkSelf
    computeOf
    referenceArgs
    sentinel
    stubEngine
    providesSelf
    projectionArgs
    projectionSelf
    multiArgs
    multiSelf
    reverseComputeOf
    reverseArgs
    reverseSentinel
    reverseStubEngine
    gatherSelf
    reverseNullSelf
    reverseNonNullSelf
    ;
}
