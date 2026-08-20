# PURITY INVARIANT: gen-view's library source depends only on gen-prelude and gen-graph, and
# imports NO `nixpkgs.lib`. This pins "pure" as a CHECKED property rather than an aspiration — a
# stray `lib.foo` / `lib.types` / `evalModules` / nixpkgs reference creeping into the library
# source fails CI rather than being noticed later by a consumer whose own evaluation breaks.
#
# Scope: lib/**.nix plus the root flake.nix and default.nix — the library and its entries. NOT
# `ci/`, where the harness legitimately uses the nixpkgs lib, including to run this scan.
#
# ★ COMMENT-STRIPPING IS LOAD-BEARING HERE AND NOT A COURTESY TO DOCUMENTATION. The forbidden list
# contains ordinary words, and this library's source is heavily prose: the header of
# `placement.nix` states that the gen libraries are nixpkgs-lib-free, which is a TRUE SENTENCE that
# trips the raw scan. A purity scan that fails on true prose gets weakened by whoever meets it
# next, and the weakening lands on the TOKEN LIST rather than on the predicate — which is how a
# scan quietly stops checking the thing it was written for.
#
# ★★ THE ABSENCE CLAIM CARRIES A POSITIVE CONTROL IN THE SAME RUN, ON THE SAME PREDICATE, OVER THE
# SAME CORPUS. An empty `violations` is a claim that a scan found nothing; without a control it is
# equally consistent with a scan that COULD find nothing — a mistyped path, an empty file list, a
# predicate that cannot match. The control is a token that IS in the stripped source, run through
# the same `hasInfix` over the same `sources`, and it must be non-empty.
{
  genPrelude,
  lib,
  ...
}:
let
  libDir = ../../lib;

  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  nixFiles = lib.filter (lib.hasSuffix ".nix") (lib.attrNames (builtins.readDir libDir));
  sources =
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

  # Tokens that signal a nixpkgs-lib tether or the module-system tier.
  forbidden = [
    "nixpkgs"
    "lib."
    "{ lib }"
    "{ lib,"
    "evalModules"
    "mkOption"
  ];

  hits = tok: lib.filter (src: genPrelude.hasInfix tok src.code) sources;

  violations = lib.concatMap (tok: map (src: "${src.name}: '${tok}'") (hits tok)) forbidden;
in
{
  flake.tests.purity.test-library-source-is-nixpkgs-lib-free = {
    expr = violations;
    expected = [ ];
  };

  # THE POSITIVE CONTROL. `prelude` is the injected substrate's own name and appears in the CODE of
  # every module here, so the same predicate over the same corpus must find it. A run where this
  # reads empty has not measured an absence — it has measured a broken instrument.
  flake.tests.purity.test-control-the-scan-can-find-a-token-that-is-there = {
    expr = builtins.length (hits "prelude") > 3;
    expected = true;
  };

  # And the corpus is the one intended: the scan reaches every module of the library plus both
  # entries, so a file added to `lib/` is covered without anyone remembering to list it.
  flake.tests.purity.test-control-the-corpus-covers-every-library-module = {
    expr = builtins.length sources == builtins.length nixFiles + 2 && builtins.length nixFiles >= 11;
    expected = true;
  };
}
