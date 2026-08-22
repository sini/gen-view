# REFERENCE RESOLUTION — the cells whose subject is the DELEGATION itself, and the disposal the
# delegate performs that no cell of the construct's own could see.
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

    # ══ ORACLE O9 — THE MULTI-CANDIDATE DISPOSAL IS PINNED ══
    #
    # ★★★ THE CELL EVERY OTHER ORACLE HERE IS BLIND TO. D < I < P orders the three SORTS — local,
    # imported, inherited — and orders NOTHING among the imports. When two imported candidates are
    # both admitted, the authority disposes them BY THE RUNTIME TYPE OF THE PROJECTED DATUM, and
    # the two arms below are that disposal measured rather than described:
    #
    #   (i)  an ATTRSET projection ⇒ a shadow-fold across EVERY candidate. The expected value
    #        `{ a = 1; b = 2; }` EXISTS AT NEITHER `A` NOR `B` — which is what makes this arm
    #        discriminating: an implementation returning either node's datum fails it. It is also
    #        why no `codomain` literal is published: the cardinality is one and the PROVENANCE is
    #        not, so a constant asserting "at most one declaration" would be false in the sense it
    #        claimed.
    #   (ii) anything else ⇒ the FIRST in traversal order, which is the caller's own DECLARED
    #        imports list. `[ "a" ]` comes back and `B` is SILENTLY ABSENT. This is the live
    #        consumer's type.
    #
    # ★★ ARM (ii) DOES NOT DISCRIMINATE ON ITS OWN AND THIS CELL SAYS SO. Under a degeneration that
    # simply dropped `B`, arm (ii) would still read `[ "a" ]`. What protects it is arm (i) SHARING
    # THE FIXTURE — the same graph, the same two admitted candidates — together with `q` below. A
    # cell claiming otherwise would be claiming a control it does not have.
    test-a-multi-candidate-import-set-is-disposed-by-the-authority = {
      expr = {
        attrsAtR = f.multiSelf.get "r" "attrsArm";
        listAtR = f.multiSelf.get "r" "listArm";
      };
      expected = {
        attrsAtR = {
          a = 1;
          b = 2;
        };
        listAtR = [ "a" ];
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
  };
}
