# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-view is a function of two named values — gen-prelude (the pure utility base) and gen-graph
# (the labelled-query engine). Defaults fetch the flake-locked revs (content-addressed via
# narHash, so the plain-import path stays pure and in lockstep with the flake output). Pass either
# explicitly to override, e.g. a local checkout.
#
# ★ THIS SHIM NAMES EXACTLY THE FORMALS `lib/default.nix` NAMES, AND THAT IS THE WHOLE POINT OF
# THE FILE. A shim naming FEWER arguments than the library it delegates to is not a lockstep entry
# — it is a second signature that nothing compares against the first, and it can promise lockstep
# in its own comment while `import ./.` throws `called without required argument`. That class has
# fired repeatedly in this ecosystem, always the same way: every suite builds the library by
# importing `../lib` directly, so the ROOT entry is evaluated by nothing and drifts green forever.
# `ci/tests/entry.nix` is what evaluates it here.
#
# ★★ THE DEFAULTS ARE READ THROUGH `root.inputs`, BY LABEL, NEVER BY NODE-KEY SPELLING. A lock's
# node KEY is a disambiguated name: a second instance of a library becomes `gen-prelude_2`, and
# which key the ROOT's own input got is not something a reader can infer from the spelling.
# `lock.nodes.root.inputs.<label>` is the edge the root actually resolves; indexing
# `lock.nodes.<label>` reads whatever node happens to hold that key.
#
# ★ `graph` IS BUILT FROM THE SAME `prelude` THIS SHIM RESOLVED, which the flake's
# `inputs.gen-prelude.follows` makes the same construction the flake output holds. Were the two
# preludes allowed to diverge, this entry and the flake output would be two libraries that agree
# on names and disagree on builds — the one drift an `attrNames` comparison cannot see.
#
# ★ `graph` IS CONSTRUCTED THROUGH GEN-GRAPH'S OWN STANDALONE ENTRY, NEVER THROUGH ITS BARE
# `./lib`. Reaching past the entry obliged this file to name gen-graph's whole formal list by
# hand, which is a SECOND SIGNATURE that nothing compares against the first: every formal
# gen-graph gains or retires has to be re-tracked here, and when it drifts only the standalone
# path breaks while CI — which exercises the flake path — stays green. Through the entry, what
# gen-graph needs is defaulted by gen-graph from its own lock and the divergence cannot form.
{
  lock ? builtins.fromJSON (builtins.readFile ./flake.lock),
  fetch ? name: builtins.fetchTree lock.nodes.${lock.nodes.root.inputs.${name}}.locked,
  prelude ? import "${fetch "gen-prelude"}/lib",
  graph ? import "${fetch "gen-graph"}" { inherit prelude; },
}:
import ./lib { inherit prelude graph; }
