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

  # ★ THE STRIP'S PREMISE, asserted rather than assumed. `stripComments` cuts each line at a comment
  # marker, and that cut is sound only while the `#` it cuts at stands OUTSIDE a string literal.
  # Where it does not, live code is truncated to the end of that line and every cell below goes
  # blind on what was removed, with no signal at all — a green suite over source nothing scanned.
  #
  # The predicate asks the strip ITSELF where it cut: `stripComments` of a single line is exactly
  # the text before that line's cut. It then asks whether that text closed every double quote it
  # opened, an odd count meaning the cut stands inside a string. Deriving it from `stripComments`
  # rather than restating the cut rule is what keeps premise and strip from drifting apart when one
  # of them is edited, and it is why one block serves both strip families in this ecosystem.
  #
  # It is LINE-LOCAL and so cannot conclude about string content that spans lines — an indented
  # multi-line string block. Those files are declared as a list of their own by
  # `test-strip-premise-multiline-strings` rather than trusted in silence.
  countQuotes = s: (lib.length (lib.splitString "\"" s)) - 1;
  cutIsInString =
    line:
    let
      kept = stripComments line;
    in
    kept != line && lib.mod (countQuotes kept) 2 == 1;

  # premiseBreaches : [ { name; text; } ] -> [ "file:line" ]. A breach is reported at its line as
  # well as its file, because what it says is that one particular line's code was truncated.
  premiseBreaches =
    srcs:
    lib.concatMap (
      src:
      lib.concatLists (
        lib.imap1 (i: line: lib.optional (cutIsInString line) "${src.name}:${toString i}") (
          lib.splitString "\n" src.text
        )
      )
    ) srcs;

  # ★ THE WALK DESCENDS, AND CARRIES ITS PREFIX. A flat `readDir` sees `lib/` one level deep, so a
  # file added under a new subdirectory leaves the invariant SILENTLY — the scan reports clean over a
  # tree it no longer covers, which is the failure this scope is written to exclude rather than to
  # survive. `lib/` is flat today, so the invariant cell exercises the recursive branch not at all;
  # `test-walk-descends-into-subdirectories` is what holds it.
  #
  # Labels are repo-root-relative paths, never bare basenames: `lib/default.nix` and the root
  # `default.nix` are both in scope and a bare basename names them with the same string, so a red CI
  # would name a file the reader cannot open. The walk therefore carries a prefix down from the root
  # it was handed.
  walk =
    prefix: dir:
    lib.concatLists (
      lib.mapAttrsToList (
        entry: type:
        if type == "directory" then
          walk "${prefix}${entry}/" (dir + "/${entry}")
        else if lib.hasSuffix ".nix" entry then
          [
            {
              name = "${prefix}${entry}";
              path = dir + "/${entry}";
            }
          ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  # ★ THE READ AND THE STRIP ARE SEPARATE STAGES, one `readFile` per file feeding both. The premise
  # cell has to speak about the RAW text, which is only a value once the strip stops happening inside
  # the read; and `sources` is then a total per-element function of `rawSources` — the name passes
  # through, the code is the strip of the text — so pinning either one pins the other, and the cells
  # over each COMPOSE instead of hoping two independent reads of the same tree agree.
  raw =
    entries:
    map (e: {
      inherit (e) name;
      text = builtins.readFile e.path;
    }) entries;

  strip =
    entries:
    map (e: {
      inherit (e) name;
      code = stripComments e.text;
    }) entries;

  libEntries = walk "lib/" libDir;

  rawSources = raw libEntries ++ [
    {
      name = "flake.nix";
      text = builtins.readFile ../../flake.nix;
    }
    {
      name = "default.nix";
      text = builtins.readFile ../../default.nix;
    }
  ];

  sources = strip rawSources;

  # Tokens that signal a nixpkgs-lib tether or the module-system tier.
  forbidden = [
    "nixpkgs"
    "lib."
    "{ lib }"
    "{ lib,"
    "evalModules"
    "mkOption"
  ];

  hitsIn = srcs: tok: lib.filter (src: genPrelude.hasInfix tok src.code) srcs;
  hits = hitsIn sources;

  scan = srcs: lib.concatMap (tok: map (src: "${src.name}: '${tok}'") (hitsIn srcs tok)) forbidden;

  violations = scan sources;
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
    expr =
      builtins.length sources == builtins.length libEntries + 2 && builtins.length libEntries >= 11;
    expected = true;
  };
  # THE WALK DESCENDS, AND CARRIES ITS PREFIX. lib/ is flat today, so the invariant cell exercises
  # the recursive branch not at all and would keep passing if the walk quietly flattened — which is
  # precisely the state this replaced. The fixture tree is nested on purpose and carries a planted
  # tether at each of its two depths; handing the walk a non-empty prefix pins both halves of the
  # naming rule, that the given prefix is threaded through and that a subdirectory's prefix extends
  # it rather than replacing it.
  flake.tests.purity.test-walk-descends-into-subdirectories = {
    expr = scan (strip (raw (walk "ci/tests/_fixtures/purity-walk/" ./_fixtures/purity-walk)));
    expected = [
      "ci/tests/_fixtures/purity-walk/nested/tethered.nix: 'lib.'"
      "ci/tests/_fixtures/purity-walk/surface.nix: 'mkOption'"
    ];
  };

  # ★ THE PREMISE HOLDS OF THE TEXT THAT WAS ACTUALLY SCANNED. This is an absence claim over text
  # read from disk and it is NOT non-vacuous on its own: its expectation is `[ ]`, which an emptied
  # or constant subject satisfies exactly as a sound corpus does — a scan of nothing breaches no
  # premise. What arms it is the subject-pinning asserted over this same `rawSources` read, together
  # with the live control below for the predicate itself; green here means the premise holds of the
  # text those cells pin, and nothing more.
  flake.tests.purity.test-strip-premise-holds = {
    expr = premiseBreaches rawSources;
    expected = [ ];
  };

  # And the predicate is capable of saying no. Its subject is a literal written inside this cell
  # rather than anything on disk, so it is UNSEVERABLE from the tree and establishes exactly that the
  # test discriminates an in-string `#` from an ordinary trailing comment — it says nothing whatever
  # about what the cell above was pointed at, and it is NOT that cell's arming. Both directions ride
  # in one expectation: line 1 must be caught and line 2 must not, so a predicate stuck at either
  # constant reds here. The literal cuts under BOTH strip families in this ecosystem — its `#` is
  # whitespace-preceded, so a comment-start strip cuts there too and the control cannot go dead by
  # being pasted into a repository whose strip is the other one.
  flake.tests.purity.test-strip-premise-scan-is-live = {
    expr = premiseBreaches [
      {
        name = "<in-string-hash>";
        text = ''
          url = "a b # c";
          x = 1; # an ordinary trailing comment
        '';
      }
    ];
    expected = [ "<in-string-hash>:1" ];
  };

  # The declared surface: the files the line-local predicate cannot conclude about. An indented
  # multi-line string block carries string content across line boundaries, where a per-line quote
  # count cannot follow it, so those files are written down rather than trusted in silence. The first
  # file to grow one arrives as a red that has to be READ, exactly as a new library file arrives as a
  # red on a membership manifest.
  flake.tests.purity.test-strip-premise-multiline-strings = {
    expr = map (s: s.name) (lib.filter (s: genPrelude.hasInfix "''" s.text) rawSources);
    expected = [ ];
  };
}
