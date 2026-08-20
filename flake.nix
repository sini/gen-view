{
  description = "gen-view: the substrate's derived-view constructor — the (L, E, <, k) carrier with van Antwerpen's relation sort published as a raw calculus, and the named compositions over it";

  # TWO dependencies, both pure and nixpkgs-lib-free: gen-prelude (the utility base) and gen-graph
  # (the labelled-query engine whose Brzozowski-derivative kernel this library's label
  # well-formedness element steps its expressions with — CITED RATHER THAN REINVENTED).
  #
  # ★ THE `follows` IS LOAD-BEARING, NOT HYGIENE. Without it gen-graph resolves its own gen-prelude
  # and the lock carries TWO instances of one library, disambiguated to `gen-prelude_2`. The two
  # are then different values, and a plain-import consumer reading a lock node by its bare label
  # gets whichever node happens to hold that key. One prelude in the closure means the shim's
  # `graph` and the flake's `graph` are the same construction rather than two that happen to agree.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph = {
      url = "github:sini/gen-graph";
      inputs.gen-prelude.follows = "gen-prelude";
    };
  };

  # The test runner lives in ./ci, which is a separate flake.
  outputs =
    { gen-prelude, gen-graph, ... }:
    {
      lib = import ./lib {
        prelude = gen-prelude.lib;
        graph = gen-graph.lib;
      };
    };
}
