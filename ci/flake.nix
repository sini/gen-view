{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph = {
      url = "github:sini/gen-graph";
      inputs.gen-prelude.follows = "gen-prelude";
    };
    # ★★ gen-scope IS A TEST DEPENDENCY AND ONLY A TEST DEPENDENCY, ON THE SAME TERMS AS nixpkgs
    # BELOW. `referenceResolution` takes its query authority as an INJECTED FIELD, so the library
    # reaches no evaluator and `../flake.nix` gains no edge onto one — which is the property that
    # keeps this library evaluator-free, and `ci/tests/reference.nix` asserts it over the library's
    # own source rather than leaving it to this comment. What the ORACLES need is different and
    # cannot be faked: the delegation cell must show the REAL authority answering where a stub's
    # sentinel comes back, and the multi-candidate cell asserts the REAL delegate's disposal
    # values. A hand-written engine would make both cells assertions about the fixture.
    gen-scope = {
      url = "github:sini/gen-scope";
      inputs.gen-prelude.follows = "gen-prelude";
      inputs.gen-graph.follows = "gen-graph";
    };
    # nixpkgs is the CI runner's dependency (nix-unit harness, treefmt) and supplies the `lib` the
    # test modules use — including to run the purity scan itself. It enters ONLY in ci/, never as a
    # `lib/` dep: the library (../lib) is nixpkgs-lib-free, which ci/tests/purity.nix enforces.
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{
      gen-harness,
      gen-prelude,
      gen-graph,
      gen-scope,
      ...
    }:
    let
      prelude = import "${gen-prelude}/lib";
      graph = import "${gen-graph}/lib" { inherit prelude; };
      genView = import ../lib { inherit prelude graph; };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-view";
      # `testModules` is the whole of `flake.tests`, and `flake.tests` is the whole of what the
      # batch asserter behind `checks.default` quantifies over. Cells that assert an ERROR cannot
      # live there — the asserter forces `expr` unconditionally, so a throwing `expr` crashes the
      # gate rather than failing a cell. They are therefore outside this tree BY CONSTRUCTION, on
      # their own output: `./tests-error.nix`, read by `nix-unit --flake ./ci#testsError`.
      testModules = ./tests;
      # The harness's own `genPrelude` carries `hasInfix` and nothing else. The purity scan needs
      # that; the suites that build fixtures need the WHOLE prelude, and they get gen-view's own —
      # the same instance the library under test was built from, so the suites and the subject
      # share one build rather than holding two.
      specialArgs = {
        inherit genView graph;
        genPrelude = prelude;
        # The REAL query authority the reference cells inject. It is handed to the construct as a
        # field, exactly as a consumer hands it one; nothing in `../lib` reaches it.
        genScope = gen-scope.lib;
      };
      extraModules = [ ./tests-error.nix ];
    };
}
