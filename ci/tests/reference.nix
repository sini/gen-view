# REFERENCE RESOLUTION — the cells whose subject is the DELEGATION itself, and the refusal of a
# multi-candidate import set the delegate raises that no cell of the construct's own could see.
#
# The refusals live next door in `refusals.nix` (the boolean half) and in `ci/tests-error.nix` (the
# message half), on this library's standing split. What is here is everything the construct claims
# about the authority it does not implement.
{
  genView,
  genScope,
  genPrelude,
  lib,
  ...
}:
let
  f = import ../reference-fixture.nix { inherit genView genScope; };

  # ── THE INJECTION SCAN ──
  # The same construction `purity.nix` uses next door, over the same corpus, under a different
  # token set: that scan asks whether the library is nixpkgs-lib-free, this one asks whether it
  # reaches a query authority. Two invariants with two reasons, so two predicates rather than one
  # widened token list a later reader would have to un-merge.
  libDir = ../../lib;

  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  nixFiles = lib.filter (lib.hasSuffix ".nix") (lib.attrNames (builtins.readDir libDir));
  libSources =
    map (name: {
      inherit name;
      code = stripComments (builtins.readFile (libDir + "/${name}"));
    }) nixFiles
    ++ [
      {
        name = "flake.nix";
        code = stripComments (builtins.readFile ../../flake.nix);
      }
      {
        name = "default.nix";
        code = stripComments (builtins.readFile ../../default.nix);
      }
    ];

  # The control corpus: the CI flake, which declares the very input the library must not carry.
  ciSources = [
    {
      name = "ci/flake.nix";
      code = stripComments (builtins.readFile ../flake.nix);
    }
  ];

  # The two spellings by which the authority could be reached — the flake input's label and the
  # binding every consumer of it uses.
  authorityTokens = [
    "gen-scope"
    "genScope"
  ];

  hitsIn =
    sources:
    lib.concatMap (
      tok: map (src: "${src.name}: '${tok}'") (lib.filter (src: genPrelude.hasInfix tok src.code) sources)
    ) authorityTokens;

  violations = hitsIn libSources;

  # The authority's refusal is a named `throw`, so a caller can hold it. Spelled exactly as
  # `refusals.nix` spells its own: one predicate for one property, whoever authored the refusal.
  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;
in
{
  flake.tests.reference = {
    # ══ ORACLE O3 — THE DELEGATION IS HONEST ══
    #
    # ★★★ THE SEEDED-DEFECT ORACLE FOR THE ANTI-DRIFT CONDITION, and the cell a later author will
    # meet. The construct is handed an authority whose `query` IGNORES ITS ARGUMENTS and answers a
    # sentinel; `compute` must return that sentinel. It can only do so while the answer is entirely
    # the authority's — the moment any part of the resolution is computed inside the construct, the
    # sentinel stops coming back. This is what fails if a shadowing decision is ever "optimized"
    # into `lib/reference.nix`.
    #
    # ★ THE CONTROL IS THE REAL AUTHORITY OVER THE SAME DECLARATION IN THE SAME EVALUATOR. Without
    # it the cell is consistent with a construct that returns whatever it is handed and resolves
    # nothing at all — a sentinel coming back from a construct that never queries anything is not
    # evidence of delegation, it is evidence of a short circuit.
    test-the-compute-is-the-authoritys-answer-and-nothing-else = {
      expr = {
        stub = f.providesSelf.get "req" "stubbed";
        real = f.providesSelf.get "req" "resolved";
      };
      expected = {
        stub = f.sentinel;
        real = [
          "read"
          "write"
        ];
      };
    };

    # ★ AND THE RESOLUTION WALKS THE IMPORT EDGE RATHER THAN READING A LOCAL DATUM. The requirer's
    # own `provided` is empty, so it is not a binding and the answer must come from the node it
    # includes. A construct that answered the local datum would satisfy the cell above on a fixture
    # where the two agreed; here they do not.
    test-control-the-answer-comes-from-the-included-provider = {
      expr = {
        requirerResolves = f.providesSelf.get "req" "resolved";
        providerResolves = f.providesSelf.get "prov" "resolved";
      };
      expected = {
        requirerResolves = [
          "read"
          "write"
        ];
        providerResolves = [
          "read"
          "write"
        ];
      };
    };

    # ══ ORACLE O9 — THE MULTI-CANDIDATE IMPORT SET IS REFUSED BY THE AUTHORITY ══
    #
    # ★★★ THE CELL EVERY OTHER ORACLE HERE IS BLIND TO. D < I < P orders the three SORTS — local,
    # imported, inherited — and orders NOTHING among the imports. `r` includes both `A` and `B` and
    # both are admitted, so the authority is handed a candidate set the specificity ordering does
    # not decide. It answers with a single declaration or REFUSES: two admitted candidates
    # contributed by two DISTINCT nodes are two declaration occurrences for one read, which is an
    # ambiguity (Neron 2015 §2.2, Duplicate Declarations), and it refuses by name.
    #
    # ★★ WHAT THIS CELL PINS IS THAT THE REFUSAL TRAVELS. `referenceResolution`'s compute is TOTAL
    # DELEGATION, so it neither authors this refusal nor may swallow it — a construct that caught
    # the throw and answered anything at all would be deciding among declarations, which is the one
    # thing the delegation exists not to do. The cell reads the refusal through the construct,
    # which is the only place the property is observable from here.
    #
    # ★★ BOTH ARMS ARE CAUGHT SEPARATELY, AND THAT IS DELIBERATE. One `tryEval` over both reads
    # would be satisfied by a construction in which only one of them refused. The two projections
    # reach the authority by different types — `d` is attrset-valued, `l` is list-valued and is the
    # live consumer's type — and until this change those were two different code paths carrying two
    # different silent dispositions: a shadow-fold across every candidate producing a value that
    # existed at NEITHER node, and `builtins.head` in traversal order with `B` silently absent.
    # Asserting each arm separately is what keeps the retirement of both of them oracled.
    test-a-multi-candidate-import-set-is-refused-by-the-authority = {
      expr = {
        attrsAtR = refuses (f.multiSelf.get "r" "attrsArm");
        listAtR = refuses (f.multiSelf.get "r" "listArm");
      };
      expected = {
        attrsAtR = true;
        listAtR = true;
      };
    };

    # ★★ THE CONTROL, AND IT IS A NODE WITH EXACTLY ONE ADMITTED IMPORT. `q` includes only `A`, so
    # it exercises THE SAME IMPORT PATH as `r` and answers one node's own datum in both type arms.
    # A control node with NO imports would answer its own LOCAL datum and never enter the import
    # path at all — it would pass while the import walk was dead, which is the weaker claim this
    # cell exists not to make.
    test-control-a-single-admitted-import-answers-that-nodes-datum = {
      expr = {
        attrsAtQ = f.multiSelf.get "q" "attrsArm";
        listAtQ = f.multiSelf.get "q" "listArm";
      };
      expected = {
        attrsAtQ = {
          a = 1;
        };
        listAtQ = [ "a" ];
      };
    };

    # ══ THE AUTHORITY IS INJECTED, AS A CHECKED FACT OVER THE LIBRARY'S OWN SOURCE ══
    #
    # ★★★ WHAT KEEPS THIS LIBRARY EVALUATOR-FREE IS THE INJECTION, AND AN INJECTION IS ONLY WORTH
    # ANYTHING WHILE NOTHING REACHES THE AUTHORITY ANOTHER WAY. The cells above build the construct
    # against the real delegate, which arrives through `ci/flake.nix` — a TEST dependency on the
    # same terms as nixpkgs. That distinction is invisible from the cells themselves: a library
    # that quietly grew an import of the authority would pass every one of them. This is the cell
    # that reads `../../lib` instead.
    #
    # ★ COMMENT-STRIPPING IS LOAD-BEARING HERE FOR THE REASON `purity.nix` STATES NEXT DOOR: the
    # construct's own header NAMES the delegate repeatedly, in true sentences, because pointing at
    # the authority is exactly what it does instead of reimplementing it. A scan that failed on
    # true prose would get weakened by whoever met it next, and the weakening would land on the
    # token list rather than on the predicate.
    test-the-library-source-reaches-no-query-authority = {
      expr = violations;
      expected = [ ];
    };

    # THE POSITIVE CONTROL, SAME PREDICATE, SAME RUN, over a corpus the token IS in: `ci/flake.nix`
    # declares the very input the library must not carry. A run where this reads empty has not
    # measured an absence — it has measured a broken instrument.
    test-control-the-authority-scan-finds-the-token-where-it-belongs = {
      expr = builtins.length (hitsIn ciSources) > 0;
      expected = true;
    };

    # And the corpus is the one intended: every module of the library plus both entries, so a file
    # added to `lib/` is covered without anyone remembering to list it.
    test-control-the-authority-scan-covers-every-library-module = {
      expr = builtins.length libSources == builtins.length nixFiles + 2 && builtins.length nixFiles >= 12;
      expected = true;
    };

    # ══ ORACLE O6 — THE REVERSE DELEGATION IS HONEST, AND ITS ENGINE CHECK NAMES ITS OWN OPERATOR ══
    #
    # ★★★ THE SEEDED-DEFECT ORACLE, ONE RELATION OVER. The construct is handed an authority whose
    # `queryReverse` IGNORES ITS ARGUMENTS and answers a sentinel; `compute` must return that
    # sentinel, which it can do only while the answer is entirely the authority's. The moment any
    # part of the reverse walk — an importer enumeration, a closure step, a fold — is computed
    # inside `lib/reference.nix`, the sentinel stops coming back.
    #
    # ★ THE CONTROL IS THE REAL AUTHORITY OVER THE SAME DECLARATION IN THE SAME EVALUATOR. Without
    # it the cell is consistent with a construct that returns whatever it is handed and gathers
    # nothing at all: a sentinel coming back from a construct that never queries anything is
    # evidence of a short circuit, not of delegation.
    test-the-reverse-compute-is-the-authoritys-answer-and-nothing-else = {
      expr = {
        stub = f.gatherSelf.get "db1" "stubbed";
        real = f.gatherSelf.get "db1" "direct";
      };
      expected = {
        stub = f.reverseSentinel;
        real = [
          "w1"
          "w2"
          "m"
        ];
      };
    };

    # ══ ORACLE O2 — THE GATHER, ASSERTED ON THE VALUE ══
    #
    # ★★ THREE CONTRIBUTORS, AND THE COUNT IS THE DISCRIMINATION. `web1`, `web2` and `mid` all
    # import `db1`. A construct that answered the FIRST contributor gives `[ "w1" ]` here and a
    # construct that answered the origin's own datum gives `[ ]`; a three-element expectation
    # rejects both. This is the shape the forward arm cannot have — there the delegate REFUSES a
    # candidate set it cannot order, and here it gathers one with no refusal at all, which is the
    # measured reason the two directions are two constructs rather than one field.
    test-the-reverse-gather-answers-every-importer = {
      expr = f.gatherSelf.get "db1" "direct";
      expected = [
        "w1"
        "w2"
        "m"
      ];
    };

    # ★ AND THE ANSWER IS THE CONTRIBUTORS' DATUM RATHER THAN THEIR IDENTITY, which is a claim about
    # `project`'s domain and not about the walk. The same fixture under a different π answers the
    # ids — a different π, a different answer — so the datum arm above cannot be an artefact of a
    # gather that reached one thing and named it twice.
    test-control-a-different-projection-over-one-gather-answers-differently = {
      expr = f.gatherSelf.get "db1" "identities";
      expected = [
        "web1"
        "web2"
        "mid"
      ];
    };

    # ══ ORACLE O3 — AN EMPTY GATHER IS NOT A REFUSAL ══
    #
    # ★★ THE EXACT INVERSION OF THIS LIBRARY'S LAW, AND IT IS WHY THE CELL CARRIES BOTH ARMS.
    # Nothing imports `web2`, so its reverse answer is empty — and empty is the ORDINARY case of a
    # reverse gather, not an exceptional one. A construct that refused here would have made a
    # refusal out of an ordinary absence, which is the failure `refusal.nix` exists to forbid in the
    # other direction. The populated node in the same run is what keeps the empty from being the
    # answer of a walk that never ran.
    test-a-node-with-no-importers-gathers-empty-without-refusing = {
      expr = {
        empty = f.gatherSelf.get "web2" "direct";
        refused = refuses (f.gatherSelf.get "web2" "direct");
        populated = f.gatherSelf.get "db1" "direct";
      };
      expected = {
        empty = [ ];
        refused = false;
        populated = [
          "w1"
          "w2"
          "m"
        ];
      };
    };

    # ══ ORACLE O4 — `transitive` IS DECLARED AND CHANGES THE ANSWER ══
    #
    # ★★ TWO ARMS OVER ONE FIXTURE, AND THEY ARE EACH OTHER'S CONTROL: a construct that dropped the
    # field on the floor would give one value twice. `web1` imports `db1` directly AND imports
    # `mid`, which imports `db1` — two reverse paths to one node.
    #
    # ★★★ THE DUPLICATE `w1` IS ASSERTED, NOT TOLERATED. The delegate does not deduplicate, because
    # a reverse gather COUNTS CONTRIBUTIONS, and a caller needing a set does that at its own call
    # site. A construct that deduplicated here would be this library performing a fold the delegate
    # owns — the anti-drift condition broken — and this expectation is what fails then.
    test-the-transitive-arm-is-declared-and-changes-the-answer = {
      expr = {
        direct = f.gatherSelf.get "db1" "direct";
        transitive = f.gatherSelf.get "db1" "transitive";
      };
      expected = {
        direct = [
          "w1"
          "w2"
          "m"
        ];
        transitive = [
          "w1"
          "w2"
          "m"
          "w1"
        ];
      };
    };

    # ══ ADR-0026 — THE BOUNDARY MARK IS THE FAIL-CLOSED FLOOR, COMPILED AT THE ACCESSOR ══
    #
    # ★★★ THE WITNESS. Before `marks` existed the consumer's declaration read THROUGH a boundary
    # the calculus draws: `req`'s own mark refuses `imports`, and the answer was the provider's
    # tags. Bounded, the edge is absent and the answer is the delegate's "no binding". The three
    # controls are what stop a bound that withheld everything from passing: no marks, a mark at
    # another node, and a mark at `req` refusing a different label all leave the answer whole.
    test-a-mark-at-the-requirer-withholds-the-import = {
      expr = {
        sealed = f.boundarySelf.get "req" "sealed";
        unmarked = f.boundarySelf.get "req" "unmarked";
        markedElsewhere = f.boundarySelf.get "req" "markedElsewhere";
        otherLabel = f.boundarySelf.get "req" "otherLabel";
      };
      expected = {
        sealed = null;
        unmarked = [
          "read"
          "write"
        ];
        markedElsewhere = [
          "read"
          "write"
        ];
        otherLabel = [
          "read"
          "write"
        ];
      };
    };

    # ★ THE INHERITED CANDIDATE IS BOUNDED TOO — the P-edge is the node record's `parent`, and a
    # mark at `child` refusing `parent` withholds it. A mark refusing `imports` there leaves it.
    test-a-mark-on-parent-withholds-the-inherited-candidate = {
      expr = {
        unmarked = (f.v.referenceResolution f.referenceArgs).compute f.parentRecord "child";
        sealed =
          (f.v.referenceResolution (f.referenceArgs // { marks = f.sealAt "child" "parent"; })).compute
            f.parentRecord
            "child";
        importsSealed =
          (f.v.referenceResolution (f.referenceArgs // { marks = f.sealAt "child" "imports"; })).compute
            f.parentRecord
            "child";
      };
      expected = {
        unmarked = [ "ambient" ];
        sealed = null;
        importsSealed = [ "ambient" ];
      };
    };

    # ★★★ `neededBy` IS THE INVERSE OF WHAT `referenceResolution` READS, UNDER THE SAME MARKS. The
    # owner-ruled definition is "the stated inverse of `includes`", and a boundary is an ABSENT
    # edge, absent in both directions. So a mark classifies the edge at the IMPORTER, the node it
    # leaves: sealed at `req`, `req` reads nothing and nothing is needed by it; sealed at `prov`,
    # `req` still reads `prov` and `prov` is still needed by `req`. Classifying at the target
    # instead answers `[ "r" ]` / `[ ]` on those two rows, and `[ "m" ]` on the two-hop one.
    test-neededby-is-the-inverse-of-what-referenceresolution-reads = {
      expr = {
        none = {
          reads = (f.dual f.noMarks).get "req" "reads";
          neededBy = (f.dual f.noMarks).get "prov" "neededBy";
        };
        sealedAtImporter = {
          reads = (f.dual (f.sealAt "req" "imports")).get "req" "reads";
          neededBy = (f.dual (f.sealAt "req" "imports")).get "prov" "neededBy";
        };
        sealedAtTarget = {
          reads = (f.dual (f.sealAt "prov" "imports")).get "req" "reads";
          neededBy = (f.dual (f.sealAt "prov" "imports")).get "prov" "neededBy";
        };
        twoHopNone = {
          reads = (f.twoHop f.noMarks).get "app" "reads";
          neededBy = (f.twoHop f.noMarks).get "lib" "neededBy";
        };
        twoHopSealedAtMiddle = {
          reads = (f.twoHop (f.sealAt "mid" "imports")).get "app" "reads";
          neededBy = (f.twoHop (f.sealAt "mid" "imports")).get "lib" "neededBy";
        };
      };
      expected = {
        none = {
          reads = [ "secret" ];
          neededBy = [ "r" ];
        };
        sealedAtImporter = {
          reads = null;
          neededBy = [ ];
        };
        sealedAtTarget = {
          reads = [ "secret" ];
          neededBy = [ "r" ];
        };
        twoHopNone = {
          reads = [ "L" ];
          neededBy = [
            "m"
            "a"
          ];
        };
        twoHopSealedAtMiddle = {
          reads = null;
          neededBy = [ ];
        };
      };
    };

    # ★ THE GATHER UNDER MARKS: `lib`'s mark governs `lib`'s own imports and not its importers', so
    # a seal there leaves the gather whole; a seal at `web1` removes exactly `web1`.
    test-a-mark-governs-the-edges-leaving-its-node-in-the-reverse-gather = {
      expr = {
        unmarked = (f.libGatherSelf f.noMarks).get "lib" "gathered";
        sealedAtLib = (f.libGatherSelf (f.sealAt "lib" "imports")).get "lib" "gathered";
        sealedAtWeb1 = (f.libGatherSelf (f.sealAt "web1" "imports")).get "lib" "gathered";
      };
      expected = {
        unmarked = [
          "w1"
          "w2"
        ];
        sealedAtLib = [
          "w1"
          "w2"
        ];
        sealedAtWeb1 = [ "w2" ];
      };
    };

    # ★★ ADR-0026'S DIAGNOSTIC: A REFUSAL AT A BOUNDARY NAMES THE MARK THAT CAUSED IT. Forward, at
    # the sealed node, for each channel; reverse, at the gathered node, naming the IMPORTER whose
    # mark withheld its edge — and empty where the importers' edges stand.
    test-withheld-names-the-mark-that-withheld-the-edge = {
      expr = {
        imports =
          (f.v.referenceResolution (f.referenceArgs // { marks = f.sealAt "req" "imports"; })).withheld
            f.boundarySelf
            "req";
        parent =
          (f.v.referenceResolution (f.referenceArgs // { marks = f.sealAt "child" "parent"; })).withheld
            f.parentRecord
            "child";
        reverse =
          (f.v.neededBy (f.reverseArgs // { marks = f.sealAt "web1" "imports"; })).withheld
            (f.libGatherSelf f.noMarks)
            "lib";
        reverseSealedAtTarget =
          (f.v.neededBy (f.reverseArgs // { marks = f.sealAt "lib" "imports"; })).withheld
            (f.libGatherSelf f.noMarks)
            "lib";
      };
      expected = {
        imports = [
          {
            label = "imports";
            target = "prov";
            marks = [ "isolationBoundary" ];
          }
        ];
        parent = [
          {
            label = "parent";
            target = "outer";
            marks = [ "isolationBoundary" ];
          }
        ];
        reverse = [
          {
            from = "web1";
            label = "imports";
            target = "lib";
            marks = [ "isolationBoundary" ];
          }
        ];
        reverseSealedAtTarget = [ ];
      };
    };

    # ★ NARROWING NEVER WIDENS. Over an authority already behind a bound, the construct's own bound
    # intersects: the same seal twice is one seal, and neither layer re-admits what the other
    # withheld. No case is written for an already-bounded authority, and this is why none is owed.
    test-narrowing-an-already-bounded-authority-never-widens = {
      expr = {
        sameTwice = f.compiledSelf.get "req" "sameTwice";
        innerOnly = f.compiledSelf.get "req" "innerOnly";
        outerOnly = f.compiledSelf.get "req" "outerOnly";
        neither = f.compiledSelf.get "req" "neither";
      };
      expected = {
        sameTwice = null;
        innerOnly = null;
        outerOnly = null;
        neither = [
          "read"
          "write"
        ];
      };
    };

    # ★★ σ AND π SEE THE AUTHORITY'S OWN RECORD. A π reading `parent` at a node whose own datum
    # decides answers the real parent under a `parent` seal; only the delegate's P-STEP sees the
    # narrowed one, which the inherited-candidate cell above pins.
    test-wellformed-and-project-read-the-unbounded-record = {
      expr = {
        sealed =
          (f.v.referenceResolution (
            f.referenceArgs
            // {
              marks = f.sealAt "child" "parent";
              project = x: [ x.parent ];
            }
          )).compute
            f.localParentRecord
            "child";
        unmarked =
          (f.v.referenceResolution (f.referenceArgs // { project = x: [ x.parent ]; })).compute
            f.localParentRecord
            "child";
      };
      expected = {
        sealed = [ "outer" ];
        unmarked = [ "outer" ];
      };
    };

    # ★★ THE BOUND IS A PROJECTION, NOT A FILTERED VIEW. An authority reading P through `node` is
    # bounded; one reading it through `allNodes` — a member the bound does not narrow — is REFUSED
    # rather than handed an unbounded second path. So are a relation other than `imports` and a
    # record with no `parent`; the in-protocol read over the same stub answers.
    test-a-read-outside-the-bound-is-refused = {
      expr = {
        viaNodeSealed =
          (f.v.referenceResolution (
            f.referenceArgs
            // {
              engine = f.viaNode;
              marks = f.sealAt "child" "parent";
            }
          )).compute
            f.allNodesRecord
            "child";
        viaNodeUnmarked =
          (f.v.referenceResolution (f.referenceArgs // { engine = f.viaNode; })).compute f.allNodesRecord
            "child";
        viaAllNodes = refuses (
          (f.v.referenceResolution (
            f.referenceArgs
            // {
              engine = f.viaAllNodes;
              marks = f.sealAt "child" "parent";
            }
          )).compute
            f.allNodesRecord
            "child"
        );
        unknownRelation = refuses (
          (f.v.referenceResolution (f.referenceArgs // { engine = f.viaIncludes; })).compute
            (f.stubRecord true)
            "x"
        );
        noParent = refuses (
          (f.v.referenceResolution (f.referenceArgs // { engine = f.viaImports; })).compute
            (f.stubRecord false)
            "x"
        );
        inProtocol =
          (f.v.referenceResolution (f.referenceArgs // { engine = f.viaImports; })).compute
            (f.stubRecord true)
            "x";
      };
      expected = {
        viaNodeSealed = null;
        viaNodeUnmarked = "outer";
        viaAllNodes = true;
        unknownRelation = true;
        noParent = true;
        inProtocol = [ "y" ];
      };
    };

    # ── THE `marks` FIELD: REQUIRED, UNDEFAULTED, AND OF ONE SHAPE ──
    # Omission is swept per field in `refusals.nix`; here the shape, on both constructs, beside the
    # complete declaration constructing.
    test-a-marks-field-of-the-wrong-shape-refuses = {
      expr = {
        forwardList = refuses (f.v.referenceResolution (f.referenceArgs // { marks = [ ]; }));
        forwardFormals = refuses (f.v.referenceResolution (f.referenceArgs // { marks = { id }: [ ]; }));
        reverseList = refuses (f.v.neededBy (f.reverseArgs // { marks = [ ]; }));
        forwardMissing = refuses (f.v.referenceResolution (removeAttrs f.referenceArgs [ "marks" ]));
        reverseMissing = refuses (f.v.neededBy (removeAttrs f.reverseArgs [ "marks" ]));
        control = refuses (f.v.referenceResolution f.referenceArgs);
      };
      expected = {
        forwardList = true;
        forwardFormals = true;
        reverseList = true;
        forwardMissing = true;
        reverseMissing = true;
        control = false;
      };
    };
  };
}
