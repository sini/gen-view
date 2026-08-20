{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph = {
      url = "github:sini/gen-graph";
      inputs.gen-prelude.follows = "gen-prelude";
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
      };
      extraModules = [ ./tests-error.nix ];
    };
}
