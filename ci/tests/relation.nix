# THE MATERIALIZATION, STEP BY STEP — the projection, the competition, the tie-set dispositions,
# the dedup records and the fold.
#
# Each cell here measures ONE step of the construction the oracles quantify over, so a failure
# names the step rather than the whole pipeline.
{ genView, graph, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  scopesOf = r: map (c: c.scope) r.contributions;

  # ── A DIAMOND WITH A SHORTCUT, for the projection ──
  # `a` is reachable from `d` in ONE hop and in TWO, and both arrivals sit in the SAME derivative
  # state — `parent*` steps to `parent*` — so they share a ⟨node, derivative-state⟩ class and the
  # projection has something to fold.
  dLabels = v.edgeLabels { letters = [ "parent" ]; };
  dRelations = v.relations { names = [ "import" ]; };
  dAdmission = v.labelWellFormedness {
    alphabet = dLabels;
    expression = "parent*";
  };
  dOrder = v.labelOrder {
    alphabet = dLabels;
    layers = [ [ "parent" ] ];
    endOfPath = -1;
  };
  # The diamond's OWN identity mark. `f.identityMark` is built over the fixture's two letters and
  # this carrier has one, so the shared mark cannot be reused here — the alphabet seam refuses it,
  # which is the refusal doing its job on the first fixture that could have tripped over it.
  dMark = v.labelOrder {
    alphabet = dLabels;
    layers = [ [ "parent" ] ];
    endOfPath = 0;
  };
  dKey = v.dataOrder {
    channel = "d";
    keyOf = c: c.scope;
  };
  dCarrier = v.carrier {
    relatumLabels = f.roles;
    labels = dLabels;
    labelWellFormedness = dAdmission;
    labelOrder = dOrder;
    dataOrder = dKey;
    relations = dRelations;
  };
  diamond = v.scopeGraph {
    carrier = dCarrier;
    scopes = [
      "a"
      "b"
      "d"
    ];
    edges = {
      parent =
        id:
        {
          d = [
            "b"
            "a"
          ];
          b = [ "a" ];
        }
        .${id} or [ ];
    };
    data = f.authored {
      a = [
        {
          relation = "import";
          datum = [ "a" ];
        }
      ];
    };
  };
  diamondRelation = v.viewRelation {
    definition = v.compositions.topology {
      channel = "d";
      relation = "import";
      root = "d";
      direction = "outbound";
      admission = dAdmission;
      order = dOrder;
      wellFormed = f.admitAll;
      tieSet = v.tieSets.union;
      empty = [ ];
      combine = v.combines.listAppend;
      dedup = v.dedups.none;
    };
    graph = diamond;
    marks = f.noMarks;
    orderMark = dMark;
  };

  # ── THE DIVERGENT-AT-POSITION-0 FIXTURE, for the visibility order ──
  # `A` is reached by `include`, `D` by `parent·parent`. The two paths diverge at the FIRST
  # position on DISTINCT labels, so whether either shadows the other is decided entirely by
  # whether `<l` orders those two labels — which is the question the layers declaration answers
  # and the rank-word lift used to ignore. There is deliberately no contributor at the
  # intermediate scope, so no prefix relation can mask the outcome.
  divergentGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = [
      "S"
      "A"
      "M"
      "D"
    ];
    edges = {
      include = id: if id == "S" then [ "A" ] else [ ];
      parent =
        id:
        {
          S = [ "M" ];
          M = [ "D" ];
        }
        .${id} or [ ];
    };
    data = f.authored {
      A = [
        {
          relation = "import";
          datum = [ "a" ];
        }
      ];
      D = [
        {
          relation = "import";
          datum = [ "d" ];
        }
      ];
    };
  };
  divergentWith =
    order:
    v.viewRelation {
      definition = f.mkDefinition {
        inherit order;
        root = "S";
      };
      graph = divergentGraph;
      marks = f.noMarks;
      orderMark = f.identityMark;
    };
  divergentFlat = divergentWith f.flatOrder;
  divergentLayered = divergentWith f.order;

  # ── THE EQUAL-DEPTH SIBLING PAIR, WITH NOTHING ELSE IN THE GROUP — the structural-authority
  # spec's O3 arms A and B (den-hoag-fmj7s item 4). `A1` and `A2` are BOTH one hop from `origin`,
  # on DIFFERENT labels, and neither is a prefix of the other — unlike `divergentGraph` above
  # (`A` at length 1, `D` at length 2) and unlike the base fixture's own `inc`/`mid` pair (which
  # always competes against `root`, a longer extension of `mid`'s own path). Those two fixtures
  # can show order-dependence; neither can show it with NOTHING ELSE in the group, which is what
  # the spec's arm A needs (`shadowed = [ ]`, not merely "shadowed something else too") and what
  # arm B needs (exactly one loser, not a loser plus an unrelated deeper contender).
  siblingScopes = [
    "origin"
    "A1"
    "A2"
  ];
  siblingEdges = {
    include = id: if id == "origin" then [ "A1" ] else [ ];
    parent = id: if id == "origin" then [ "A2" ] else [ ];
  };
  siblingGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = siblingScopes;
    edges = siblingEdges;
    data = f.authored {
      A1 = [
        {
          relation = "import";
          datum = [ "from-A1" ];
        }
      ];
      A2 = [
        {
          relation = "import";
          datum = [ "from-A2" ];
        }
      ];
    };
  };
  siblingWith =
    order:
    v.viewRelation {
      definition = f.mkDefinition {
        root = "origin";
        inherit order;
      };
      graph = siblingGraph;
      marks = f.noMarks;
      orderMark = f.identityMark;
    };
  # Arm A: the FLAT order leaves the two labels tied, so `<p` calls the pair incomparable and both
  # survive — the antichain the spec's M4 calls "the correct answer for a partial order".
  siblingTied = siblingWith f.flatOrder;
  # Arm B: the LAYERED order (`include` outranks `parent`) discriminates on the arrival label
  # alone — M4's "discrimination is available and requires exactly one thing: the siblings arrive
  # by different ranked labels".
  siblingRanked = siblingWith f.order;

  # ── THE RANK-TIED DISTINCT-LABEL FIXTURE, for step 6's survival classes ──
  # `A` and `P` are one hop from `r` on DISTINCT labels of ONE rank, so their rank words are equal
  # while their label words are not; `AA` extends `A` by one more `include`. Under an order in
  # which continuing outranks stopping (`endOfPath` above the letters' shared rank), `AA` shadows
  # `A` and nothing shadows `P`. Any construction that lets `P` share `A`'s fate — by keying
  # anything on RANKS rather than LABELS — drops `P`; any that forgets the `$` branch keeps `A`.
  tiedGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = [
      "r"
      "A"
      "AA"
      "P"
    ];
    edges = {
      include =
        id:
        {
          r = [ "A" ];
          A = [ "AA" ];
        }
        .${id} or [ ];
      parent = id: if id == "r" then [ "P" ] else [ ];
    };
    data = f.authored {
      A = [
        {
          relation = "import";
          datum = [ "a" ];
        }
      ];
      AA = [
        {
          relation = "import";
          datum = [ "aa" ];
        }
      ];
      P = [
        {
          relation = "import";
          datum = [ "p" ];
        }
      ];
    };
  };
  continueOrder = v.labelOrder {
    alphabet = f.labels;
    layers = [
      [
        "include"
        "parent"
      ]
    ];
    endOfPath = 1;
  };
  tiedWith =
    order:
    v.viewRelation {
      definition = f.mkDefinition {
        root = "r";
        inherit order;
      };
      graph = tiedGraph;
      marks = f.noMarks;
      orderMark = f.identityMark;
    };
  tiedContinue = tiedWith continueOrder;

  # ── THE EXHAUSTIVE COMPETITION, for step 6's survivor set over every small group ──
  # Every group of ≤ 3 distinct label words drawn from all 13 words of length ≤ 2 over {a b c},
  # each also with its first word carried by a second member, under all 13 weak orders on the
  # letters × `endOfPath` ∈ −1..3 — so `$` sits strictly below, tied with, between and above every
  # layer. The graph is the word trie itself: scope `r` is the empty word and each other scope is
  # named by the word that reaches it, so a member's path IS its word. Each group is one registry
  # entity, so every group competes on its own inside ONE query per order.
  exLetters = [
    "a"
    "b"
    "c"
  ];
  exLabels = v.edgeLabels { letters = exLetters; };
  exWords = [ "" ] ++ exLetters ++ builtins.concatMap (x: map (y: x + y) exLetters) exLetters;
  exScopeOf = w: if w == "" then "r" else w;
  exSubsets =
    let
      go =
        start: size:
        if size == 0 then
          [ [ ] ]
        else
          builtins.concatMap (i: map (rest: [ i ] ++ rest) (go (i + 1) (size - 1))) (
            builtins.genList (j: j + start) (builtins.length exWords - start)
          );
    in
    builtins.concatMap (go 0) [
      1
      2
      3
    ];
  exMembers = builtins.concatLists (
    builtins.genList (
      g:
      let
        s = builtins.elemAt exSubsets g;
        on =
          key:
          map (i: {
            inherit key;
            w = builtins.elemAt exWords i;
          });
      in
      on "g${toString g}" s ++ on "d${toString g}" (s ++ [ (builtins.head s) ])
    ) (builtins.length exSubsets)
  );
  exAdmission = v.labelWellFormedness {
    alphabet = exLabels;
    expression = "(a|b|c)*";
  };
  exFlat = v.labelOrder {
    alphabet = exLabels;
    layers = [ exLetters ];
    endOfPath = 0;
  };
  exGraph = v.scopeGraph {
    carrier = v.carrier {
      labels = exLabels;
      inherit (f) relations;
      relatumLabels = f.roles;
      labelWellFormedness = exAdmission;
      labelOrder = exFlat;
      dataOrder = v.dataOrder {
        channel = "settings";
        keyOf = c: builtins.head c.datum;
      };
    };
    scopes = map exScopeOf exWords;
    edges = builtins.listToAttrs (
      map (l: {
        name = l;
        value =
          id:
          if id == "r" then
            [ l ]
          else if builtins.stringLength id == 1 then
            [ (id + l) ]
          else
            [ ];
      }) exLetters
    );
    data = builtins.genList (
      j:
      let
        m = builtins.elemAt exMembers j;
      in
      {
        scope = exScopeOf m.w;
        relation = "import";
        datum = [
          m.key
          (toString j)
        ];
      }
    ) (builtins.length exMembers);
  };
  exOrders =
    builtins.concatMap
      (
        layers:
        map
          (
            endOfPath:
            v.labelOrder {
              alphabet = exLabels;
              inherit layers endOfPath;
            }
          )
          [
            (-1)
            0
            1
            2
            3
          ]
      )
      [
        [ exLetters ]
        [
          [ "a" ]
          [
            "b"
            "c"
          ]
        ]
        [
          [ "b" ]
          [
            "a"
            "c"
          ]
        ]
        [
          [ "c" ]
          [
            "a"
            "b"
          ]
        ]
        [
          [
            "a"
            "b"
          ]
          [ "c" ]
        ]
        [
          [
            "a"
            "c"
          ]
          [ "b" ]
        ]
        [
          [
            "b"
            "c"
          ]
          [ "a" ]
        ]
        [
          [ "a" ]
          [ "b" ]
          [ "c" ]
        ]
        [
          [ "a" ]
          [ "c" ]
          [ "b" ]
        ]
        [
          [ "b" ]
          [ "a" ]
          [ "c" ]
        ]
        [
          [ "b" ]
          [ "c" ]
          [ "a" ]
        ]
        [
          [ "c" ]
          [ "a" ]
          [ "b" ]
        ]
        [
          [ "c" ]
          [ "b" ]
          [ "a" ]
        ]
      ];
  # Per order: each group's survivors as the query returns them, against the pairwise definition
  # over the published `pathPrecedes` on the same members.
  exCompare =
    order:
    let
      r = v.viewRelation {
        definition = v.compositions.registry {
          channel = "settings";
          relation = "import";
          root = "r";
          direction = "outbound";
          admission = exAdmission;
          inherit order;
          wellFormed = f.admitAll;
          tieSet = v.tieSets.union;
          empty = [ ];
          combine = v.combines.listAppend;
          dedup = v.dedups.none;
          entityOf = c: builtins.head c.datum;
        };
        graph = exGraph;
        marks = f.noMarks;
        orderMark = exFlat;
      };
      byGroup =
        cs:
        builtins.mapAttrs (_: ms: builtins.sort builtins.lessThan (map (c: builtins.elemAt c.datum 1) ms)) (
          builtins.groupBy (c: builtins.head c.datum) cs
        );
      all = builtins.groupBy (c: builtins.head c.datum) (r.contributions ++ r.shadowed);
      pairwise = byGroup (
        builtins.concatMap (
          ms: builtins.filter (c: !(builtins.any (o: order.pathPrecedes o.path c.path) ms)) ms
        ) (builtins.attrValues all)
      );
      visible = byGroup r.contributions;
    in
    map (g: {
      agree = (visible.${g} or [ ]) == pairwise.${g};
      decides = builtins.length pairwise.${g} < builtins.length all.${g};
    }) (builtins.attrNames all);
  exCases = builtins.concatMap exCompare exOrders;

  # ── THE PER-SCOPE-KEY RELATION OVER THE DUPLICATE GRAPH, for the dedup records ──
  dupWith =
    dedup:
    v.viewRelation {
      definition = v.viewDefinition (
        f.definitionArgs
        // {
          channel = f.perScopeKey;
          inherit dedup;
        }
      );
      graph = f.dupGraph;
      marks = f.noMarks;
      orderMark = f.identityMark;
    };

  # ── THE DECIDING PATH: A RECORDED DROP IS ONE THE DECLARATION LICENSES (den-hoag-behm0) ──
  #
  # `dedups.byDatum` declares "structural equality on the datum itself" and `dedups.byKey` "a
  # domain where two structurally distinct datums are the same thing"; in both, SAME is Nix `==`.
  # Step 8 addresses a bucket by `builtins.toJSON` and DECIDES by that relation. Deciding on the
  # encoding instead records a drop asserting a duplicate that does not exist, because `toJSON`
  # serialises an `outPath`/`__toString` attrset as its string coercion.
  #
  # ★ ONE PREDICATE SERVES BOTH ARMS, because both are the same defect stated over the arm's own
  # declared relation — which is also why `byKey` compares KEYS: under `byKey` a drop of unequal
  # DATA is the declared semantics, so "what was lost equals what was kept" is the wrong
  # discriminator there.
  coercionDatum = scope: datum: {
    inherit scope datum;
    relation = "import";
  };
  coercionGraph =
    data:
    v.scopeGraph {
      inherit (f) carrier scopes edges;
      inherit data;
    };
  # `{ outPath = "X"; }` and `"X"` are Nix-DISTINCT and `toJSON`-IDENTICAL — the collision itself.
  collideData = [
    (coercionDatum "inc" [ { outPath = "X"; } ])
    (coercionDatum "mid" [ "X" ])
  ];
  # The reference differs in EXACTLY ONE TOKEN — `inner` for `outPath` — so it does not coerce and
  # does not collide. Subject and reference disagreeing on that one token is what makes the pair a
  # measurement of the coercion rather than of the fixture.
  separateData = [
    (coercionDatum "inc" [ { inner = "X"; } ])
    (coercionDatum "mid" [ "X" ])
  ];
  identicalData = [
    (coercionDatum "inc" [ "X" ])
    (coercionDatum "mid" [ "X" ])
  ];
  distinctData = [
    (coercionDatum "inc" [ "a" ])
    (coercionDatum "mid" [ "b" ])
  ];

  # ── FUNCTION-BEARING DATA (den-hoag-eunp3) — a NixOS module is a function ──
  # `sharedModule` is ONE binding, so `[ sharedModule ] == [ sharedModule ]` is TRUE (Nix compares
  # list elements by pointer first); two literals of the same text are two closures and Nix `==`
  # calls them unequal. Both are Nix's `==`, which is the relation `dedups.byDatum` declares.
  sharedModule = { config, ... }: { };
  fnSharedData = [
    (coercionDatum "inc" [ sharedModule ])
    (coercionDatum "mid" [ sharedModule ])
  ];
  fnFreshData = [
    (coercionDatum "inc" [ ({ config, ... }: { }) ])
    (coercionDatum "mid" [ ({ config, ... }: { }) ])
  ];
  # den's aspect shape: a module under a class key. The address must reach a lambda through an
  # attrset as well as through a list.
  fnAttrData = [
    (coercionDatum "inc" [ { nixos = sharedModule; } ])
    (coercionDatum "mid" [ { nixos = sharedModule; } ])
  ];
  fnMixedData = [
    (coercionDatum "inc" [ sharedModule ])
    (coercionDatum "mid" [ "X" ])
  ];
  # A derivation-shaped datum that refers to ITSELF, as every real derivation does (`out`). The
  # address must stop at `outPath` where `toJSON` stops, or it walks this forever.
  selfDrv =
    let
      d = {
        type = "derivation";
        outPath = "/nix/store/eunp3-self";
        out = d;
      };
    in
    d;
  drvData = [
    (coercionDatum "inc" [ selfDrv ])
    (coercionDatum "mid" [ selfDrv ])
  ];
  # `toJSON` CALLS `__toString`, so the address must leave that function in place.
  toStringData = [
    (coercionDatum "inc" [ { __toString = _: "X"; } ])
    (coercionDatum "mid" [ "X" ])
  ];
  # `dropped.key` under `byDatum` is the datum's bucket address — read raw, not through the oracle.
  byDatumKeys =
    data:
    map (d: d.key)
      (v.viewRelation {
        definition = coercionDef { dedup = v.dedups.byDatum; };
        graph = coercionGraph data;
        marks = f.noMarks;
        orderMark = f.identityMark;
      }).dropped;

  # THE PREDICATE, read off the RESULT alone: `definition` is carried inside `viewRelation`'s
  # return, so the cell needs nothing the caller did not already hand it.
  noFalseDedup =
    r:
    let
      arm = r.definition.dedup.arm;
    in
    builtins.all (
      d:
      if arm == "byDatum" then
        d.contribution.datum == d.collapsedInto.datum
      else if arm == "byKey" then
        d.key == r.definition.dedup.keyOf d.collapsedInto
      else
        true
    ) r.dropped;

  # `tryEval` keeps `holds` REMEDY-NEUTRAL: a refusal recorded nothing false either, so it passes.
  # `refused` is reported SEPARATELY so a cell can pin WHICH outcome it got — at `byDatum` the
  # refuse arm is closed by the declaration (refusing a coercible datum narrows what the view can
  # carry), so the subject cell there pins `refused = false` and a narrowing remedy reds it.
  dedupOracle =
    r:
    let
      t = builtins.tryEval (builtins.deepSeq r (noFalseDedup r));
    in
    {
      holds = !t.success || t.value;
      refused = !t.success;
      kept = builtins.length r.contributions;
      dropped = builtins.length r.dropped;
    };

  # `f.flatOrder` — one layer, no letter outranks another — so `inc` and `mid` are mutually
  # incomparable and TWO contributions reach step 8. The `precondition` cells assert that before
  # any dedup arm is declared: an oracle whose fixture has ONE survivor cannot discriminate.
  coercionDef = overrides: f.mkDefinition ({ order = f.flatOrder; } // overrides);
  coercionRun =
    dedup: data:
    dedupOracle (
      v.viewRelation {
        definition = coercionDef { inherit dedup; };
        graph = coercionGraph data;
        marks = f.noMarks;
        orderMark = f.identityMark;
      }
    );
  byDatumOn = coercionRun v.dedups.byDatum;
  dedupNoneOn = coercionRun v.dedups.none;
  # Data held at [ "a" ] / [ "b" ] throughout so `byDatum` cannot fire and the KEY is the only
  # variable. In both subject and reference the caller's two keys are Nix-distinct.
  byKeyWith = keyOf: coercionRun (v.dedups.byKey { inherit keyOf; }) distinctData;

  # ══════════════════════════════════════════════════════════════════════════════════════════
  # ── §1.2's DIAMOND, AND ITS FAMILY — AUTHORSHIP-VISIBILITY (den-hoag-2vzn) ──
  #
  # `top` is reached from `leaf` by two paths whose residual derivative states differ:
  #   leaf -parent-> a -include-> top     (state after: the "started on parent" residual)
  #   leaf -include-> b -parent-> top     (state after: the "started on include" residual)
  #
  # ★★★ O0's TWO MASKERS, DEFEATED BOTH. A single-derivative-state admission (e.g. `f.admission`,
  # `(parent|include)*`) collapses both arrivals to ONE class at step 4 before step 6a ever runs —
  # `diamondAdmission` below is ASYMMETRIC so the two states stay distinct. A LAYERED label order
  # (e.g. `f.order`, gen-view's own shipped default) shadows one arrival at step 6 before 6a/6b ever
  # sees two — every declaration below states `f.flatOrder` explicitly, `ci/fixture.nix`'s existing
  # flat binding, never a custom one.
  diamondAdmission = v.labelWellFormedness {
    alphabet = f.labels;
    expression = "parent(include)*|include(parent)*";
  };

  authorshipScopes = [
    "leaf"
    "a"
    "b"
    "top"
  ];

  # `top` reached twice (the diamond); no `rival`. O0, O1, O1b, O2.
  diamondEdges = {
    parent =
      id:
      {
        leaf = [ "a" ];
        b = [ "top" ];
      }
      .${id} or [ ];
    include =
      id:
      {
        leaf = [ "b" ];
        a = [ "top" ];
      }
      .${id} or [ ];
  };
  diamondData = [
    {
      scope = "top";
      relation = "import";
      datum = [ "X" ];
    }
  ];
  diamondGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = authorshipScopes;
    edges = diamondEdges;
    data = diamondData;
  };

  # The SAME graph with `b`'s route removed — `top` reached ONCE. O1's negative control, and O4's
  # single-route subject (multiplied to two declarations below).
  singleRouteEdges = {
    parent = id: { leaf = [ "a" ]; }.${id} or [ ];
    include = id: { a = [ "top" ]; }.${id} or [ ];
  };
  singleRouteGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = authorshipScopes;
    edges = singleRouteEdges;
    data = diamondData;
  };

  # O4 — the same single route, `top`'s datum authored TWICE. Deliberately single-route: the
  # diamond graph would give 2 arrivals × 2 declarations = 4 and make the cell's 2 ambiguous.
  o4Graph = v.scopeGraph {
    carrier = f.carrier;
    scopes = authorshipScopes;
    edges = singleRouteEdges;
    data = diamondData ++ diamondData;
  };

  # ── Z / Y — O2c's discriminator, and O2/O2b's `rival` fixtures ──
  # Z: no diamond, `top` reached ONCE via `a`; `rival` reached once, same route.
  zScopes = [
    "leaf"
    "a"
    "top"
    "rival"
  ];
  zEdges = {
    parent = id: { leaf = [ "a" ]; }.${id} or [ ];
    include =
      id:
      {
        a = [
          "top"
          "rival"
        ];
      }
      .${id} or [ ];
  };
  zData = [
    {
      scope = "top";
      relation = "import";
      datum = [ "X" ];
    }
    {
      scope = "rival";
      relation = "import";
      datum = [ "R" ];
    }
  ];
  zGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = zScopes;
    edges = zEdges;
    data = zData;
  };

  # Y: Z PLUS one more route to `top` alone (`leaf -include-> b -parent-> top`) — `top` now reached
  # twice, `rival` still once. This is the ONE-PAIR-OF-EDGES difference O2c turns on, and it is also
  # O2b's group-of-3 subject (the diamond's two arrivals plus `rival`'s genuinely distinct element).
  yScopes = authorshipScopes ++ [ "rival" ];
  yEdges = {
    parent =
      id:
      {
        leaf = [ "a" ];
        b = [ "top" ];
      }
      .${id} or [ ];
    include =
      id:
      {
        leaf = [ "b" ];
        a = [
          "top"
          "rival"
        ];
      }
      .${id} or [ ];
  };
  yGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = yScopes;
    edges = yEdges;
    data = zData;
  };

  # O3 — two producers, each reached by ONE route, equal content. Not diamond-shaped: O3's question
  # is element identity across DIFFERENT producers, not path multiplicity at one.
  pqScopes = [
    "leaf"
    "p"
    "q"
  ];
  pqEdges = {
    parent =
      id:
      if id == "leaf" then
        [
          "q"
          "p"
        ]
      else
        [ ];
    include = _: [ ];
  };
  pqData = [
    {
      scope = "p";
      relation = "import";
      datum = [ "X" ];
    }
    {
      scope = "q";
      relation = "import";
      datum = [ "X" ];
    }
  ];
  pqGraph = v.scopeGraph {
    carrier = f.carrier;
    scopes = pqScopes;
    edges = pqEdges;
    data = pqData;
  };

  # The raw declaration builder shared by every cell below: asymmetric admission, flat order, a
  # CONSTANT key (`_: "settings"`) by default — O0's precondition, satisfied by construction, with
  # every field overridable by name so a cell can differ in exactly one respect.
  mkAsymDef =
    overrides:
    v.viewDefinition (
      {
        channel = v.dataOrder {
          channel = "settings";
          keyOf = _: "settings";
        };
        relation = "import";
        root = "leaf";
        direction = "outbound";
        admission = diamondAdmission;
        order = f.flatOrder;
        wellFormed = f.admitAll;
        distance = s: s.distance + 1;
        tieSet = v.tieSets.union;
        empty = [ ];
        combine = v.combines.listAppend;
        dedup = v.dedups.none;
      }
      // overrides
    );

  runOn =
    graph: definition:
    v.viewRelation {
      inherit definition graph;
      marks = f.noMarks;
      orderMark = f.identityMark;
    };

  # `true` iff forcing `expr` throws — the same catchable-refusal test §2.8's `registry-split-key-
  # refuses` cell uses, kept local so the throwing-vs-not arms live in `flake.tests` (no `checks
  # .default` crash) rather than needing one `ci/tests-error.nix` cell per tie-set arm for a message
  # that is IDENTICAL across all three (6a refuses before step 7's tieSet dispatch is ever reached).
  throws = expr: !(builtins.tryEval (builtins.deepSeq expr expr)).success;

  # ── THE ORDER FIXTURE: WALK ORDER, BUCKET ORDER AND KEEP-LAST ALL DISAGREE (den-hoag-qj233) ──
  # One scope, one entry per element of `entries`, a flat order, `union`. Each entry has its OWN
  # competition key (`k`), so competition groups are singletons and emerge in walk order, and a
  # DEDUP key `d` read by `byKey`. Step 8 buckets by `toJSON d`; with `d` walked z a z a the
  # bucket (encoding) order is the REVERSE of walk order, so a construction that emits `kept` or
  # `dropped` by bucket, or keeps the last duplicate, reads differently from the pinned rule.
  orderLabels = v.edgeLabels { letters = [ "parent" ]; };
  orderAdmission = v.labelWellFormedness {
    alphabet = orderLabels;
    expression = "parent*";
  };
  orderFlat = v.labelOrder {
    alphabet = orderLabels;
    layers = [ [ "parent" ] ];
    endOfPath = 0;
  };
  orderKey = v.dataOrder {
    channel = "cfg";
    keyOf = c: (builtins.head c.datum).k;
  };
  orderRelation =
    entries: dedup:
    v.viewRelation {
      definition = v.viewDefinition {
        channel = orderKey;
        inherit dedup;
        admission = orderAdmission;
        order = orderFlat;
        wellFormed = _: true;
        relation = "cfg";
        root = "root";
        direction = "outbound";
        distance = s: s.distance + 1;
        tieSet = v.tieSets.union;
        empty = [ ];
        combine = v.combines.listAppend;
      };
      graph = v.scopeGraph {
        carrier = v.carrier {
          labels = orderLabels;
          relations = v.relations { names = [ "cfg" ]; };
          relatumLabels = v.relatumLabels { names = [ "relatum-target" ]; };
          labelWellFormedness = orderAdmission;
          labelOrder = orderFlat;
          dataOrder = orderKey;
        };
        scopes = [ "root" ];
        edges.parent = _: [ ];
        data = builtins.genList (i: {
          scope = "root";
          relation = "cfg";
          datum = [ ({ k = "k${toString i}"; } // builtins.elemAt entries i) ];
        }) (builtins.length entries);
      };
      marks = _: [ ];
      orderMark = orderFlat;
    };
  orderTag = c: (builtins.head c.datum).tag;
  orderRead = r: {
    kept = map orderTag r.contributions;
    dropped = map (d: "${orderTag d.contribution}>${orderTag d.collapsedInto}") r.dropped;
  };
  # d walked z a z a; each tag is `d` plus its walk index.
  zaza = builtins.genList (
    i:
    let
      d = builtins.elemAt [ "z" "a" "z" "a" ] i;
    in
    {
      inherit d;
      tag = "${d}${toString i}";
    }
  ) 4;
  byOrderKey = v.dedups.byKey { keyOf = c: (builtins.head c.datum).d; };
in
{
  flake.tests.relation = {
    # ★ THE CONSTRUCTING CONTROL FOR THE DEFINITION⟂GRAPH ALPHABET SEAM. The refusing arms live in
    # `ci/tests-error.nix`'s `alphabet-seam-refusals`; these are the SAME TWO CALLS differing in
    # exactly one respect — the definition's alphabet is the graph's own rather than a foreign one —
    # so those refusals are verdicts on the ALPHABET and on nothing else. The `void` row is the one
    # that carries the weight: it materializes EMPTY, which is what makes the error plane's
    # empty-gather cell a refusal rather than a restatement of "this root has no datum".
    test-a-definition-over-the-graphs-own-alphabet-materializes-at-both-roots = {
      expr =
        let
          at =
            root:
            map (c: c.datum)
              (f.mkRelation {
                definition = f.mkDefinition { inherit root; };
                graph = f.voidGraph;
              }).contributions;
        in
        {
          rooted = at "root";
          gathersNothing = at "void";
        };
      expected = {
        rooted = [ [ "root" ] ];
        gathersNothing = [ ];
      };
    };

    # ── THE PROJECTION: A MIN-FOLD OVER `distance` WITHIN EACH ⟨node, derivative-state⟩ CLASS ──
    # Two witnesses reach `a`; one survives, and it is the nearer one. ★ A CARRIER KEYED FINER THAN
    # THE DECLARATION IS NOT A MISMATCH — the projection is part of the materialization and not a
    # chore left to the consumer.
    test-the-projection-keeps-the-nearest-arrival-in-each-class = {
      expr = map (c: {
        inherit (c) scope distance;
        word = map (s: s.label) c.path;
      }) diamondRelation.contributions;
      expected = [
        {
          scope = "a";
          distance = 1;
          word = [ "parent" ];
        }
      ];
    };

    # ★ THE CONTROL: THE FURTHER WITNESS REALLY EXISTS, measured BENEATH the projection on the same
    # walk in the same run. Without it the cell above is equally consistent with a graph on which
    # only one path to `a` was ever available — and the min-fold would then be folding one element
    # and measuring nothing.
    test-control-two-witnesses-reach-the-node-beneath-the-projection = {
      expr =
        let
          answers = graph.query {
            mode = "paths";
            graph = diamond.labeled;
            from = "d";
            follow = dAdmission.expr;
          };
          atA = builtins.filter (ans: ans.node == "a") answers;
        in
        {
          witnesses = builtins.length atA;
          lengths = builtins.sort builtins.lessThan (map (ans: builtins.length ans.path) atA);
          # And both sit in the SAME derivative state, which is what makes them one class rather
          # than two: `parent*` steps to `parent*`, at one hop and at two.
          states = builtins.sort builtins.lessThan (
            map (
              ans:
              dAdmission.stateKey (
                builtins.foldl' (st: step: dAdmission.step step.label st) dAdmission.expr ans.path
              )
            ) atA
          );
        };
      expected = {
        witnesses = 2;
        lengths = [
          1
          2
        ];
        states = [
          "'parent*"
          "'parent*"
        ];
      };
    };

    # ── COMPETITION AND SHADOWING: THE DISCARDED SET IS REPORTED, NEVER DROPPED SILENTLY ──
    test-shadowed-contributions-are-reported-not-dropped = {
      expr = {
        visible = scopesOf f.relation;
        shadowed = map (c: {
          inherit (c) scope distance;
        }) f.relation.shadowed;
      };
      expected = {
        visible = [ "inc" ];
        shadowed = [
          {
            scope = "mid";
            distance = 1;
          }
          {
            scope = "root";
            distance = 2;
          }
        ];
      };
    };

    # ── THE EQUAL-DEPTH SIBLING CASE (den-hoag-fmj7s item 4; spec §3 O3) ──
    # `A1` and `A2` are both one hop from `origin`, on different labels, and NOTHING ELSE is in the
    # competition — unlike the cell above, whose `shadowed` set is confounded by `root` (a longer
    # extension of `mid`'s own path, always shadowed regardless of order) and unlike
    # `divergentGraph` (a genuine sibling structure, but at UNEQUAL depth). O3 arm A: under a FLAT
    # order the pair is tied, `<p` calls it incomparable, and both survive as an antichain. O3 arm
    # B: under a LAYERED order the pair is discriminated on the arrival label alone, and the loser
    # is reported in `shadowed`, not dropped. (O3 arm C — siblings under `tieSets.refuse` — is
    # already landed as `materialization-refusals.test-a-refused-tie-names-the-channel-and-the-tied-scopes`
    # in `ci/tests-error.nix`; not re-landed here.)
    test-equal-depth-siblings-tie-flat-and-discriminate-layered = {
      expr = {
        tied = {
          visible = scopesOf siblingTied;
          shadowed = siblingTied.shadowed;
        };
        ranked = {
          visible = scopesOf siblingRanked;
          shadowed = map (c: {
            inherit (c) scope distance;
            datum = c.datum;
          }) siblingRanked.shadowed;
        };
      };
      expected = {
        tied = {
          visible = [
            "A1"
            "A2"
          ];
          shadowed = [ ];
        };
        ranked = {
          visible = [ "A1" ];
          shadowed = [
            {
              scope = "A2";
              distance = 1;
              datum = [ "from-A2" ];
            }
          ];
        };
      };
    };

    # ── THE TIE-SET DISPOSITIONS ──
    # `union` — the papers' own arm: the surviving-maximal set IS the answer, in walk order.
    test-union-keeps-the-whole-surviving-maximal-set = {
      expr = (f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }).value;
      expected = [
        "inc"
        "mid"
      ];
    };

    # `orderedFold` — the surviving set is disposed by the DECLARED contribution order, which
    # OVERRIDES the walk order. ★ THAT IS THE POINT: the order must be invariant under presentation
    # order, so a declaration that reverses the walk must actually reverse the result.
    test-orderedfold-disposes-by-the-declared-order-not-the-walk = {
      expr = {
        walkOrder = (f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }).value;
        declaredForward =
          (f.mkRelation {
            definition = f.mkDefinition {
              order = f.flatOrder;
              tieSet = v.tieSets.orderedFold {
                order = [
                  "inc"
                  "mid"
                ];
              };
            };
          }).value;
        declaredReversed =
          (f.mkRelation {
            definition = f.mkDefinition {
              order = f.flatOrder;
              tieSet = v.tieSets.orderedFold {
                order = [
                  "mid"
                  "inc"
                ];
              };
            };
          }).value;
      };
      expected = {
        walkOrder = [
          "inc"
          "mid"
        ];
        declaredForward = [
          "inc"
          "mid"
        ];
        declaredReversed = [
          "mid"
          "inc"
        ];
      };
    };

    # ── DEDUP: EVERY DROP IS A RECORD ──
    # The surface this replaces DECLARED a dedup and enumerated no drops, so an answer that came
    # back short could not be told from a contribution that was never made. Here the drop names the
    # contribution, the survivor it collapsed into, the policy and the key.
    test-every-dedup-drop-is-a-record = {
      expr =
        let
          r = dupWith v.dedups.byDatum;
        in
        {
          kept = map (c: {
            inherit (c) scope datum;
          }) r.contributions;
          dropped = map (d: {
            scope = d.contribution.scope;
            into = d.collapsedInto.scope;
            inherit (d) policy;
          }) r.dropped;
          value = r.value;
        };
      expected = {
        kept = [
          {
            scope = "inc";
            datum = [ "inc" ];
          }
          {
            scope = "mid";
            datum = [ "mid" ];
          }
        ];
        dropped = [
          {
            scope = "root";
            into = "mid";
            policy = "byDatum";
          }
        ];
        value = [
          "inc"
          "mid"
        ];
      };
    };

    # ★ THE CONTROL, SAME FIXTURE, SAME RUN: under `none` NOTHING IS DROPPED and the duplicate
    # survives. Without it "one drop was recorded" is consistent with a gather that only ever found
    # two contributions.
    test-control-under-the-none-policy-the-duplicate-survives-undropped = {
      expr =
        let
          r = dupWith v.dedups.none;
        in
        {
          kept = map (c: c.datum) r.contributions;
          dropped = r.dropped;
        };
      expected = {
        kept = [
          [ "inc" ]
          [ "mid" ]
          [ "mid" ]
        ];
        dropped = [ ];
      };
    };

    # A declared key collapses what structural equality would not — and records that too.
    test-a-declared-dedup-key-collapses-by-the-key = {
      expr =
        let
          r = dupWith (v.dedups.byKey { keyOf = _: "one-bucket"; });
        in
        {
          kept = map (c: c.scope) r.contributions;
          dropped = map (d: d.contribution.scope) r.dropped;
        };
      expected = {
        kept = [ "inc" ];
        dropped = [
          "mid"
          "root"
        ];
      };
    };

    # ── STEP 8's ORDERS, PINNED (den-hoag-qj233) ──
    # Step 8 buckets survivors by address, so the order of `kept` and of `dropped` and the identity
    # of the survivor are properties the construction must RESTORE, not ones it inherits. On the
    # z a z a fixture walk order, bucket order and keep-last all disagree.
    test-dedup-keeps-the-first-in-walk-order-and-records-drops-in-walk-order = {
      expr = orderRead (orderRelation zaza byOrderKey);
      expected = {
        kept = [
          "z0"
          "a1"
        ];
        dropped = [
          "z2>z0"
          "a3>a1"
        ];
      };
    };

    # A drop collapses into the FIRST kept element of its bucket that is `same`, even where `==`
    # is not transitive and a later kept element is `same` too. A, B and C all encode to `"K"` (one
    # bucket); `A == B` and `B == C` hold while `A == C` does not, so walking A C B keeps A and C, and
    # B matches BOTH. The first match is o0; a last-match slip reads `o2>o1`.
    test-dedup-collapses-into-the-first-kept-match =
      let
        keyA = {
          outPath = "K";
          n = 9007199254740993;
        };
        keyB = {
          outPath = "K";
          n = 9007199254740992.0;
        };
        keyC = {
          outPath = "K";
          n = 9007199254740992;
        };
      in
      {
        expr = {
          nonTransitive = [
            (keyA == keyB)
            (keyB == keyC)
            (keyA == keyC)
          ];
          dedup = orderRead (
            orderRelation [
              {
                d = keyA;
                tag = "o0";
              }
              {
                d = keyC;
                tag = "o1";
              }
              {
                d = keyB;
                tag = "o2";
              }
            ] byOrderKey
          );
        };
        expected = {
          nonTransitive = [
            true
            true
            false
          ];
          dedup = {
            kept = [
              "o0"
              "o1"
            ];
            dropped = [ "o2>o0" ];
          };
        };
      };

    # `transform.scan` is the INCLUSIVE prefix in walk order: each datum is the accumulation up to
    # and including its own contribution. An exclusive scan reads `[ [ ] [ "z0" ] … ]`.
    test-scan-is-the-inclusive-prefix-in-walk-order = {
      expr =
        map (c: c.datum)
          (v.transform.scan {
            relation = orderRelation zaza v.dedups.none;
            name = "scanned";
            empty = [ ];
            f = s: c: s ++ [ (orderTag c) ];
          }).contributions;
      expected = [
        [ "z0" ]
        [
          "z0"
          "a1"
        ]
        [
          "z0"
          "a1"
          "z2"
        ]
        [
          "z0"
          "a1"
          "z2"
          "a3"
        ]
      ];
    };

    # ══════════════════════════════════════════════════════════════════════════════════════
    # ── THE DEDUP DECIDES ON THE DECLARED RELATION, NEVER ON THE ENCODING (den-hoag-behm0) ──
    #
    # The cells above establish that every drop is a RECORD. These establish that the record is
    # TRUE: a `dropped` entry asserts a duplicate, and under an encoding-decided dedup it could
    # assert one that does not exist under the declaration's own equality.
    #
    # ★★ `CONTROL-genuineDuplicate` IS WHAT MAKES THIS AN ORACLE rather than a "nothing was
    # dropped" check in disguise. It drops one contribution and PASSES, because that drop is one
    # the declaration licenses. A cell asserting `dropped == 0` would pass the subject fixture the
    # moment the construction over-corrected into refusing all dedup, and would fail the corpus's
    # own legitimate collapses.

    # ── THE MULTI-SURVIVOR PRECONDITION, ASSERTED RATHER THAN ASSUMED ──
    # Under `dedups.none` both fixtures keep TWO contributions, so step 8 has something to decide.
    # Without this the subject cells below are consistent with a gather that only ever found one.
    test-the-colliding-fixture-puts-two-survivors-into-the-dedup-step = {
      expr = dedupNoneOn collideData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    test-the-separating-fixture-puts-two-survivors-into-the-dedup-step = {
      expr = dedupNoneOn separateData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    # ── `byDatum` — THE SUBJECT AND ITS ONE-TOKEN REFERENCE ──
    # `{ outPath = "X"; }` and `"X"` are Nix-UNEQUAL, so `dedups.byDatum` — "structural equality on
    # the datum itself" — licenses no collapse between them and BOTH survive.
    #
    # ★ `refused = false` is pinned HERE and only here. The refuse remedy at this arm — refusing a
    # coercible datum — narrows what the view can carry, and is closed by the declaration rather
    # than open as a choice. Pinning the outcome is what tells this construction apart from a build
    # that bought the same `holds` by narrowing admission.
    test-a-coercible-datum-is-not-deduped-into-its-string-coercion = {
      expr = byDatumOn collideData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    # THE REFERENCE, differing from the subject in one token: an attribute named `inner` rather
    # than `outPath`. It never coerced, so it reads the same before and after — which is what makes
    # the subject's move attributable to the coercion and to nothing else about the fixture.
    test-control-a-non-coercing-attrset-datum-is-not-deduped-either = {
      expr = byDatumOn separateData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    # ★ THE DISCRIMINATOR: two genuinely equal data DO collapse, one drop IS recorded, and the
    # oracle PASSES. This is the cell that fails if the construction over-corrects into dropping
    # nothing.
    test-control-two-equal-datums-still-collapse-and-the-drop-still-holds = {
      expr = byDatumOn identicalData;
      expected = {
        kept = 1;
        dropped = 1;
        holds = true;
        refused = false;
      };
    };

    test-control-two-unequal-datums-are-both-kept-under-bydatum = {
      expr = byDatumOn distinctData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    # ── `byKey` — THE SAME DEFECT AT THE CALLER'S KEY ──
    # `dedups.byKey` checks `isFunction keyOf` and nothing about its RETURN, so a caller key of
    # `{ outPath = "K"; }` reaches the fold and encodes as `"K"`. The declared relation is `==` on
    # the keys, and those two keys are Nix-unequal.
    #
    # ★ `refused` is deliberately NOT pinned at this arm: whether a deciding key must be a String
    # is an open question above this construction, and an oracle that pinned the outcome here would
    # presume its answer. `holds` admits either.
    test-a-coercible-caller-key-is-not-deduped-into-its-string-coercion = {
      expr = (byKeyWith (c: if c.scope == "inc" then { outPath = "K"; } else "K")).holds;
      expected = true;
    };

    test-control-a-non-coercing-caller-key-is-not-deduped-either = {
      expr = (byKeyWith (c: if c.scope == "inc" then { inner = "K"; } else "K")).holds;
      expected = true;
    };

    # ★ THE DISCRIMINATOR AT THIS ARM. One key for both contributions: the collapse is declared, the
    # drop is recorded, and the oracle passes — on the OPPOSITE `dropped` count from the cell above.
    test-control-one-declared-key-for-both-still-collapses-and-the-drop-still-holds = {
      expr = byKeyWith (_: "K");
      expected = {
        kept = 1;
        dropped = 1;
        holds = true;
        refused = false;
      };
    };

    test-control-two-distinct-declared-keys-are-both-kept-under-bykey = {
      expr = byKeyWith (c: c.scope);
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    # ══════════════════════════════════════════════════════════════════════════════════════
    # ── A FUNCTION-BEARING DATUM IS DEDUPED BY `==`, NEVER ABORTED ON (den-hoag-eunp3) ──
    #
    # The bucket address was `toJSON`, which aborts on a lambda where `tryEval` cannot hold it. A
    # lambda gets no identity in the address — one constant tag — and `==` still decides.
    #
    # ★ `refused = false` is pinned at `byDatum`, as for the coercion cells above: refusing a
    # function-bearing datum narrows what the view can carry. ★ The shared cell is what separates
    # this construction from one that never collapses a function-bearing datum: under `==` the
    # shared pair IS a duplicate.
    test-the-function-bearing-fixture-puts-two-survivors-into-the-dedup-step = {
      expr = dedupNoneOn fnSharedData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    test-a-shared-function-bearing-datum-collapses-under-nix-equality = {
      expr = byDatumOn fnSharedData;
      expected = {
        kept = 1;
        dropped = 1;
        holds = true;
        refused = false;
      };
    };

    test-a-shared-module-under-a-class-key-collapses-under-nix-equality = {
      expr = byDatumOn fnAttrData;
      expected = {
        kept = 1;
        dropped = 1;
        holds = true;
        refused = false;
      };
    };

    test-function-bearing-datums-nix-equality-separates-are-both-kept = {
      expr = byDatumOn fnFreshData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    test-a-function-bearing-datum-is-not-deduped-into-a-plain-one = {
      expr = byDatumOn fnMixedData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    test-a-self-referential-derivation-datum-is-addressed-at-its-outpath = {
      expr = byDatumOn drvData;
      expected = {
        kept = 1;
        dropped = 1;
        holds = true;
        refused = false;
      };
    };

    test-a-tostring-datum-is-addressed-through-its-coercion-and-kept-apart = {
      expr = byDatumOn toStringData;
      expected = {
        kept = 2;
        dropped = 0;
        holds = true;
        refused = false;
      };
    };

    # ★ THE ADDRESS IS `toJSON` BYTE-FOR-BYTE ON FUNCTION-FREE DATA, and a lambda reads as one tag.
    test-a-bydatum-drop-records-the-datum-address-as-its-key = {
      expr = {
        plain = byDatumKeys identicalData;
        function = byDatumKeys fnSharedData;
      };
      expected = {
        plain = [ (builtins.toJSON [ "X" ]) ];
        function = [ ''[{"__lambda":null}]'' ];
      };
    };

    # The same address serves `byKey`. `refused` is NOT pinned here, for the reason the coercible
    # caller-key cell gives: whether a deciding key must be a String is open above this arm.
    test-a-function-bearing-caller-key-dedups-without-aborting = {
      expr = (byKeyWith (_: [ sharedModule ])).holds;
      expected = true;
    };

    # ── THE GROUPS EMIT IN WALK-FIRST KEY ORDER ──
    # One scope, three data entries, keys spelled per entry. The competition groups by key, and
    # the groups must come out in order of each key's FIRST appearance in the walk — not its last
    # appearance, and not its spelling. `revKeys` is what separates walk-first from key spelling:
    # on `interleaved` the two coincide.
    test-groups-emit-in-walk-first-key-order = {
      expr =
        let
          labels = v.edgeLabels { letters = [ "parent" ]; };
          admission = v.labelWellFormedness {
            alphabet = labels;
            expression = "parent*";
          };
          flat = v.labelOrder {
            alphabet = labels;
            layers = [ [ "parent" ] ];
            endOfPath = 0;
          };
          key = v.dataOrder {
            channel = "cfg";
            keyOf = c: (builtins.head c.datum).k;
          };
          run =
            ks:
            let
              carrier = v.carrier {
                inherit labels;
                relations = v.relations { names = [ "cfg" ]; };
                relatumLabels = v.relatumLabels { names = [ "relatum-target" ]; };
                labelWellFormedness = admission;
                labelOrder = flat;
                dataOrder = key;
              };
              g = v.scopeGraph {
                inherit carrier;
                scopes = [ "root" ];
                edges.parent = _: [ ];
                data = builtins.genList (i: {
                  scope = "root";
                  relation = "cfg";
                  datum = [
                    {
                      k = builtins.elemAt ks i;
                      tag = "${builtins.elemAt ks i}${toString i}";
                    }
                  ];
                }) (builtins.length ks);
              };
              r = v.viewRelation {
                definition = v.viewDefinition {
                  channel = key;
                  inherit admission;
                  order = flat;
                  wellFormed = _: true;
                  relation = "cfg";
                  root = "root";
                  direction = "outbound";
                  distance = s: s.distance + 1;
                  tieSet = v.tieSets.union;
                  empty = [ ];
                  combine = v.combines.listAppend;
                  dedup = v.dedups.none;
                };
                graph = g;
                marks = _: [ ];
                orderMark = flat;
              };
            in
            {
              ordinals = map (c: c.element.ordinal) r.contributions;
              value = map (d: d.tag) r.value;
            };
        in
        {
          interleaved = run [
            "x"
            "y"
            "x"
          ];
          revKeys = run [
            "y"
            "x"
            "y"
          ];
        };
      expected = {
        interleaved = {
          ordinals = [
            0
            2
            1
          ];
          value = [
            "x0"
            "x2"
            "y1"
          ];
        };
        revKeys = {
          ordinals = [
            0
            2
            1
          ];
          value = [
            "y0"
            "y2"
            "x1"
          ];
        };
      };
    };

    # ── THE FOLD IS ASSOCIATIVE-ONLY: NO REORDER, NO DEDUP BY RANK ──
    # The list's order IS the authority, so the value is the concatenation of the surviving
    # sequence exactly as the tie-set left it. A fold that sorted its answer set — or required a
    # commutative-idempotent monoid to hide that it had — would return the other order here.
    test-the-fold-preserves-the-surviving-sequences-order = {
      expr =
        let
          r = f.mkRelation {
            definition = f.mkDefinition {
              order = f.flatOrder;
              tieSet = v.tieSets.orderedFold {
                order = [
                  "mid"
                  "inc"
                ];
              };
            };
          };
        in
        {
          contributions = map (c: c.scope) r.contributions;
          value = r.value;
        };
      expected = {
        contributions = [
          "mid"
          "inc"
        ];
        value = [
          "mid"
          "inc"
        ];
      };
    };

    # ── THE OTHER COMBINE ARMS FOLD WHAT THEY DECLARE ──
    test-the-set-semilattice-arm-is-idempotent-over-the-surviving-sequence = {
      expr =
        (f.mkRelation {
          definition = v.viewDefinition (
            f.definitionArgs
            // {
              channel = f.perScopeKey;
              combine = v.combines.setUnion { acc = true; };
            }
          );
          graph = f.dupGraph;
        }).value;
      expected = [
        "inc"
        "mid"
      ];
    };

    # ── DIRECTION: THE INBOUND ARM WALKS THE LABELLED TRANSPOSE ──
    # Transpose REVERSES direction rather than erasing it: the label is carried BY the edge, so
    # flipping the edge relation moves the label with it, and the same admission expression still
    # applies. From `root`, the inbound walk reaches `mid` and then `leaf`.
    test-the-inbound-arm-walks-the-labelled-transpose = {
      expr =
        let
          r = f.mkRelation {
            definition = v.viewDefinition (
              f.definitionArgs
              // {
                channel = f.perScopeKey;
                root = "root";
                direction = "inbound";
              }
            );
          };
        in
        map (c: {
          inherit (c) scope distance;
        }) r.contributions;
      expected = [
        {
          scope = "root";
          distance = 0;
        }
        {
          scope = "mid";
          distance = 1;
        }
      ];
    };

    # ★ THE CONTROL: THE OUTBOUND ARM OVER THE SAME ROOT REACHES SOMETHING ELSE. Without it, an
    # inbound answer is consistent with a direction field nothing reads.
    test-control-the-outbound-arm-over-the-same-root-differs = {
      expr =
        let
          r = f.mkRelation {
            definition = v.viewDefinition (
              f.definitionArgs
              // {
                channel = f.perScopeKey;
                root = "root";
                direction = "outbound";
              }
            );
          };
        in
        map (c: c.scope) r.contributions;
      expected = [ "root" ];
    };

    # ── THE RESULT IS NAMED, AND THE NAME IS THE COMPETITION KEY'S OWN ──
    # What competes is exactly what is named, which is why the two are one field at the composition
    # surface.
    test-the-result-carries-its-name = {
      expr = {
        relation = f.relation.name;
        definition = f.relation.definition.name;
      };
      expected = {
        relation = "settings";
        definition = "settings";
      };
    };

    # ══ FLAT ORDER ⇒ NOTHING SHADOWED, END TO END ══
    #
    # ★★★ THIS IS THE FIXTURE THE DEFECT WAS FOUND ON. `A` is reached by `include` and `D` by
    # `parent·parent` — two paths that DIVERGE AT POSITION 0 on distinct labels. Under a FLAT order
    # those labels share a rank, so Fig. 1 leaves the paths incomparable and NOTHING may shadow.
    # The rank-word lift ordered them anyway and produced an outcome identical to the layered
    # control, so declaring no specificity at all shadowed exactly as much as declaring a real
    # ranking — which made the whole layers design unobservable from the answer.
    #
    # ★ THE LAYERED ARM IS IN THE SAME CELL ON PURPOSE. It is the control: with `include` ranked
    # above `parent` the two labels ARE comparable, shadowing IS licensed, and it happens. A fix
    # that simply stopped ordering things would take this half red.
    test-a-flat-order-shadows-nothing-and-a-layered-one-still-does = {
      expr = {
        flatVisible = map (c: c.scope) divergentFlat.contributions;
        flatShadowed = map (c: c.scope) divergentFlat.shadowed;
        flatValue = divergentFlat.value;
        layeredVisible = map (c: c.scope) divergentLayered.contributions;
        layeredShadowed = map (c: c.scope) divergentLayered.shadowed;
        layeredValue = divergentLayered.value;
      };
      expected = {
        flatVisible = [
          "A"
          "D"
        ];
        flatShadowed = [ ];
        flatValue = [
          "a"
          "d"
        ];
        layeredVisible = [ "A" ];
        layeredShadowed = [ "D" ];
        layeredValue = [ "a" ];
      };
    };

    # ★★ THE DIFFERENTIAL CONTROL ON THE PREFIX MINIMUM. The competition computes minimality as a
    # prefix minimum over label words — a member survives iff its symbol has the minimum rank at
    # every node of its word·$ — which rests on `<p` deciding at the first label divergence. This
    # cell runs the DIRECT pairwise definition ("nothing in the group strictly precedes it") over
    # the published `pathPrecedes` on the same groups and asserts the two agree. If the
    # characterisation were wrong, the two would disagree here rather than in a consumer's answer
    # six libraries away.
    test-control-the-bounded-minimality-scan-agrees-with-the-pairwise-definition = {
      expr =
        builtins.all
          (
            case:
            let
              members = case.relation.contributions ++ case.relation.shadowed;
              order = case.relation.definition.order;
              pairwise = builtins.filter (
                c: !(builtins.any (o: order.pathPrecedes o.path c.path) members)
              ) members;
            in
            map (c: c.scope) pairwise == map (c: c.scope) case.relation.contributions
          )
          [
            { relation = divergentFlat; }
            { relation = divergentLayered; }
            { relation = f.relation; }
            { relation = f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; }; }
            { relation = tiedContinue; }
            { relation = tiedWith f.flatOrder; }
          ];
      expected = true;
    };

    # ★ THE SURVIVAL CLASS IS THE LABEL WORD, NEVER THE RANK WORD. `A` and `P` have one rank word
    # and different label words; `AA` shadows `A` through the `$` branch, and `P` survives because
    # nothing diverges from it on a lower-ranked label. Pinned by scope, so a construction that
    # shares fate across a rank tie (drops `P`) or forgets the end-of-path branch (keeps `A`) reds
    # here as well as in the differential cell above.
    test-a-rank-tie-between-distinct-labels-does-not-share-survival = {
      expr = {
        visible = scopesOf tiedContinue;
        shadowed = map (c: c.scope) tiedContinue.shadowed;
      };
      expected = {
        visible = [
          "AA"
          "P"
        ];
        shadowed = [ "A" ];
      };
    };

    # ★ AND THE CONTROL'S OWN CONTROL: the four cases are not all trivially one-element groups, so
    # the agreement above is over groups where minimality has something to decide.
    test-control-the-differential-cases-have-competing-groups = {
      expr = map (r: builtins.length (r.contributions ++ r.shadowed)) [
        divergentFlat
        divergentLayered
        f.relation
        tiedContinue
      ];
      expected = [
        2
        2
        3
        3
      ];
    };

    # ★★ THE EXHAUSTIVE DIFFERENTIAL. The cells above agree on fixed fixtures; this one agrees on
    # EVERY group of ≤ 3 words of length ≤ 2 over three letters, under every weak order and every
    # place `$` can sit, through the query itself. `cases` pins the enumeration so a dead generator
    # cannot read as agreement, and `decided` counts the groups in which minimality shadowed
    # something, so the agreement is not over groups where every member survives. Driven red: a
    # node keyed by the RANK prefix agrees on 44606, one without the `$` branch on 34298.
    test-control-the-prefix-minimum-agrees-with-the-pairwise-definition-exhaustively = {
      expr = {
        cases = builtins.length exCases;
        agree = builtins.length (builtins.filter (x: x.agree) exCases);
        decided = builtins.length (builtins.filter (x: x.decides) exCases);
      };
      expected = {
        cases = 49010;
        agree = 49010;
        decided = 42252;
      };
    };

    # ══ AUTHORSHIP-VISIBILITY (den-hoag-2vzn) — §3's oracles ══

    # ★★★ O0 — THE PRECONDITION EVERY DIAMOND ORACLE BELOW DEPENDS ON. Three declarations, one
    # graph, differing in EXACTLY the field each masker owns. The two masked arms read the SAME
    # `n = 1` regardless of which library evaluates them — a single-derivative-state admission
    # collapses both arrivals at step 4 before 6a/6b ever sees two, and a layered order shadows one
    # at step 6 before 6a/6b ever sees two — so their non-discrimination is exhibited here directly,
    # not asserted. The discriminating arm's RED reading (`n = 2`) is driven separately, against a
    # stashed `lib/`, and recorded in the build report; GREEN is measured here.
    test-o0-two-maskers-each-hide-the-diamond-defect = {
      expr =
        let
          summarize = r: {
            n = builtins.length r.contributions;
            inherit (r) value;
            shadowed = builtins.length r.shadowed;
          };
        in
        {
          discriminating = summarize (runOn diamondGraph (mkAsymDef { }));
          maskedBySymmetricAdmission = summarize (
            runOn diamondGraph (mkAsymDef {
              admission = f.admission;
            })
          );
          maskedByLayeredOrder = summarize (
            runOn diamondGraph (mkAsymDef {
              order = f.order;
            })
          );
        };
      expected = {
        discriminating = {
          n = 1;
          value = [ "X" ];
          shadowed = 0;
        };
        maskedBySymmetricAdmission = {
          n = 1;
          value = [ "X" ];
          shadowed = 0;
        };
        maskedByLayeredOrder = {
          n = 1;
          value = [ "X" ];
          shadowed = 1;
        };
      };
    };

    # ── O1 — A diamond mints exactly ONE element, and the collapsed arrival is recorded NOWHERE ──
    # Asserts the count, the coordinate, the value, `shadowed` AND the survivor's `admission` — the
    # last is the only thing in §3 that pins WHICH arrival 6b keeps (walk-first, never walk-last).
    test-o1-diamond-mints-exactly-one-element = {
      expr =
        let
          r = runOn diamondGraph (mkAsymDef { });
          control = runOn singleRouteGraph (mkAsymDef { });
        in
        {
          n = builtins.length r.contributions;
          element = (builtins.head r.contributions).element;
          value = r.value;
          shadowed = builtins.length r.shadowed;
          survivorAdmission = (builtins.head r.contributions).admission;
          controlN = builtins.length control.contributions;
          controlValue = control.value;
        };
      expected = {
        n = 1;
        element = {
          producer = "top";
          ordinal = 0;
        };
        value = [ "X" ];
        shadowed = 0;
        survivorAdmission = "'parent*";
        controlN = 1;
        controlValue = [ "X" ];
      };
    };

    # ★ THE CONTROL, BENEATH THE PROJECTION: both arrivals really exist and really differ in
    # residual admission state, so O1's `n = 1` is a fold and not a fixture with one route.
    test-control-o1-diamond-has-two-distinguishable-arrivals-before-collapse = {
      expr =
        let
          answers = graph.query {
            mode = "paths";
            graph = diamondGraph.labeled;
            from = "leaf";
            follow = diamondAdmission.expr;
          };
          atTop = builtins.filter (ans: ans.node == "top") answers;
          stateOf =
            ans:
            diamondAdmission.stateKey (
              builtins.foldl' (st: step: diamondAdmission.step step.label st) diamondAdmission.expr ans.path
            );
        in
        {
          witnesses = builtins.length atTop;
          states = builtins.sort builtins.lessThan (map stateOf atTop);
        };
      expected = {
        witnesses = 2;
        states = [
          "'include*"
          "'parent*"
        ];
      };
    };

    # ── O1b — ★★★ A COMPETITION KEY THAT SPLITS AN ELEMENT IS REFUSED BY NAME ──
    # O1's fixture, `keyOf = c: c.admission` — the one element's two arrivals fall into TWO
    # competition groups. Nothing else in this suite reaches step 6a.
    test-o1b-a-split-competition-key-refuses-by-name = {
      expr =
        let
          splitChannel = v.dataOrder {
            channel = "settings";
            keyOf = c: c.admission;
          };
          defWith =
            tieSet:
            mkAsymDef {
              channel = splitChannel;
              inherit tieSet;
            };
        in
        {
          throwsUnderUnion = throws (runOn diamondGraph (defWith v.tieSets.union)).value;
          throwsUnderRefuse = throws (runOn diamondGraph (defWith v.tieSets.refuse)).value;
          throwsUnderOrderedFold =
            throws
              (runOn diamondGraph (defWith (v.tieSets.orderedFold { order = [ "top" ]; }))).value;
        };
      expected = {
        throwsUnderUnion = true;
        throwsUnderRefuse = true;
        throwsUnderOrderedFold = true;
      };
    };

    # ★ LIVE CONTROLS, SAME RUN: a merely path-READING key is not enough to reach 6a. Both give ONE
    # group on this fixture and must NOT refuse — this is O2's GREEN on the same fixture, so without
    # this arm O1b would pass for a step 6a that refuses everything.
    test-control-o1b-path-reading-keys-do-not-split-the-element = {
      expr =
        let
          byScope = v.dataOrder {
            channel = "settings";
            keyOf = c: c.scope;
          };
          byPathShape = v.dataOrder {
            channel = "settings";
            keyOf = c: "d${toString c.distance}-${toString (builtins.length c.path)}";
          };
          rScope = runOn diamondGraph (mkAsymDef {
            channel = byScope;
          });
          rShape = runOn diamondGraph (mkAsymDef {
            channel = byPathShape;
          });
        in
        {
          scopeKeyed = {
            n = builtins.length rScope.contributions;
            value = rScope.value;
          };
          shapeKeyed = {
            n = builtins.length rShape.contributions;
            value = rShape.value;
          };
        };
      expected = {
        scopeKeyed = {
          n = 1;
          value = [ "X" ];
        };
        shapeKeyed = {
          n = 1;
          value = [ "X" ];
        };
      };
    };

    # ★ NEGATIVE CONTROL, SAME RUN: it is the CONSTANT key that keeps O0's own reading out of 6a —
    # its layered-order arm already reads `n = 1, shadowed = 1` with no refusal (O0, above).
    # ★★ MEASURED THIS ROUND, AND STATED BECAUSE IT CONTRADICTS A LITERAL READING OF §3's OWN
    # WORDING: swapping the layered order onto the genuinely SPLIT key (`keyOf = c: c.admission`)
    # does NOT recover that reading. Grouping is a function of `keyOf` alone, fixed at step 6 before
    # `order` is ever consulted for ranking — so a split key gives two SINGLETON groups under
    # EITHER order, and a singleton group has nothing in it to shadow. The refusal fires under both
    # orders; that is 6a's independence from `order`, exhibited rather than assumed, and it is the
    # honest reading of "layered order + split key" on this construction.
    test-control-o1b-the-split-key-refuses-under-either-label-order = {
      expr =
        let
          splitChannel = v.dataOrder {
            channel = "settings";
            keyOf = c: c.admission;
          };
          flatSplit = runOn diamondGraph (mkAsymDef {
            channel = splitChannel;
          });
          layeredSplit = runOn diamondGraph (mkAsymDef {
            channel = splitChannel;
            order = f.order;
          });
          layeredConstant = runOn diamondGraph (mkAsymDef {
            order = f.order;
          });
        in
        {
          flatSplitThrows = throws flatSplit.value;
          layeredSplitThrows = throws layeredSplit.value;
          layeredConstantN = builtins.length layeredConstant.contributions;
          layeredConstantShadowed = builtins.length layeredConstant.shadowed;
        };
      expected = {
        flatSplitThrows = true;
        layeredSplitThrows = true;
        layeredConstantN = 1;
        layeredConstantShadowed = 1;
      };
    };

    # ── O2 — The same diamond does not trip `tieSets.refuse` ──
    # Two positive controls (different producers under refuse; two separate declarations at one
    # producer under refuse), both required to keep throwing at GREEN — without them O2 would pass
    # for a `refuse` arm that stopped firing.
    test-o2-diamond-does-not-trip-tieset-refuse = {
      expr =
        let
          r = runOn diamondGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          differentProducers = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          twoDeclarationsOneProducer = runOn o4Graph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          singleArrival = runOn singleRouteGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
        in
        {
          n = builtins.length r.contributions;
          value = r.value;
          differentProducersThrows = throws differentProducers.value;
          twoDeclarationsOneProducerThrows = throws twoDeclarationsOneProducer.value;
          singleArrivalThrows = throws singleArrival.value;
          singleArrivalN = builtins.length singleArrival.contributions;
          singleArrivalValue = singleArrival.value;
        };
      expected = {
        n = 1;
        value = [ "X" ];
        differentProducersThrows = true;
        twoDeclarationsOneProducerThrows = true;
        singleArrivalThrows = false;
        singleArrivalN = 1;
        singleArrivalValue = [ "X" ];
      };
    };

    # ── O2b — ★★ Every tie-set arm is total on a group the collapse REDUCES ──
    # `Y` is the RED subject (one group of 3: the diamond's two arrivals plus `rival`'s distinct
    # element); `Z` is the GREEN post-collapse twin (the same group reduced to 2). All four arms,
    # both graphs, in one run — four throw and four do not, so neither arm of the instrument is
    # stuck.
    test-o2b-every-tieset-arm-is-total-on-the-reduced-group = {
      expr =
        let
          unionY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.union;
          });
          unionZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.union;
          });
          refuseY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          refuseZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.refuse;
          });
          unrankedY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold { order = [ "rival" ]; };
          });
          unrankedZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold { order = [ "rival" ]; };
          });
          rankedY = runOn yGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold {
              order = [
                "rival"
                "top"
              ];
            };
          });
          rankedZ = runOn zGraph (mkAsymDef {
            tieSet = v.tieSets.orderedFold {
              order = [
                "rival"
                "top"
              ];
            };
          });
        in
        {
          unionY = {
            n = builtins.length unionY.contributions;
            value = unionY.value;
          };
          unionZ = {
            n = builtins.length unionZ.contributions;
            value = unionZ.value;
          };
          refuseYThrows = throws refuseY.value;
          refuseZThrows = throws refuseZ.value;
          unrankedYThrows = throws unrankedY.value;
          unrankedZThrows = throws unrankedZ.value;
          rankedY = {
            n = builtins.length rankedY.contributions;
            value = rankedY.value;
          };
          rankedZ = {
            n = builtins.length rankedZ.contributions;
            value = rankedZ.value;
          };
        };
      expected = {
        unionY = {
          n = 2;
          value = [
            "X"
            "R"
          ];
        };
        unionZ = {
          n = 2;
          value = [
            "X"
            "R"
          ];
        };
        refuseYThrows = true;
        refuseZThrows = true;
        unrankedYThrows = true;
        unrankedZThrows = true;
        rankedY = {
          n = 2;
          value = [
            "R"
            "X"
          ];
        };
        rankedZ = {
          n = 2;
          value = [
            "R"
            "X"
          ];
        };
      };
    };

    # ── O3 — Two equal-content declarations at DIFFERENT producers stay two ──
    # The RED arm is exhibited by an EXISTING declared policy (`dedups.byDatum`) rather than a
    # mutation, so it is available at both states: the cell fails if the collapse ever reaches
    # content.
    test-o3-equal-content-at-different-producers-stays-two = {
      expr =
        let
          r = runOn pqGraph (mkAsymDef { });
          contentKeyed = runOn pqGraph (mkAsymDef {
            dedup = v.dedups.byDatum;
          });
        in
        {
          n = builtins.length r.contributions;
          producers = map (c: c.element.producer) r.contributions;
          elements = map (c: c.element) r.contributions;
          distinctElements =
            (builtins.elemAt r.contributions 0).element != (builtins.elemAt r.contributions 1).element;
          value = r.value;
          dropped = builtins.length r.dropped;
          contentKeyedN = builtins.length contentKeyed.contributions;
          contentKeyedDropped = builtins.length contentKeyed.dropped;
        };
      expected = {
        n = 2;
        producers = [
          "q"
          "p"
        ];
        elements = [
          {
            producer = "q";
            ordinal = 1;
          }
          {
            producer = "p";
            ordinal = 0;
          }
        ];
        distinctElements = true;
        value = [
          "X"
          "X"
        ];
        dropped = 0;
        contentKeyedN = 1;
        contentKeyedDropped = 1;
      };
    };

    # ── O4 — Two equal-content declarations at ONE producer stay two ──
    # This is the cell `ordinal` exists for: the two elements agree on `producer` and on content,
    # and nothing but the component position separates them.
    test-o4-equal-content-at-one-producer-stays-two = {
      expr =
        let
          r = runOn o4Graph (mkAsymDef { });
          contentKeyed = runOn o4Graph (mkAsymDef {
            dedup = v.dedups.byDatum;
          });
        in
        {
          n = builtins.length r.contributions;
          producers = map (c: c.scope) r.contributions;
          ordinals = map (c: c.element.ordinal) r.contributions;
          value = r.value;
          contentKeyedN = builtins.length contentKeyed.contributions;
          contentKeyedDropped = builtins.length contentKeyed.dropped;
        };
      expected = {
        n = 2;
        producers = [
          "top"
          "top"
        ];
        ordinals = [
          0
          1
        ];
        value = [
          "X"
          "X"
        ];
        contentKeyedN = 1;
        contentKeyedDropped = 1;
      };
    };

    # ── O5 — Every element coordinate comes from the COMPONENT, and nothing else does ──
    # The projection is stated because the two shapes are NOT the same attrset: an entry is
    # `{ scope; relation; datum; ordinal; }`, an element coordinate is `{ producer; ordinal; }`. The
    # cell asserts `nEntries`, the coordinate list AND membership — membership alone passes
    # vacuously against an empty contribution set.
    test-o5-element-coordinates-come-from-the-component = {
      expr =
        let
          coordsOf =
            r:
            map (e: {
              producer = e.scope;
              inherit (e) ordinal;
            }) (builtins.concatMap (s: r.graph.datumsAt.${s} or [ ]) r.graph.scopes);
          check =
            r:
            let
              coords = coordsOf r;
            in
            {
              nEntries = builtins.length coords;
              inherit coords;
              membershipHolds = builtins.all (c: builtins.elem c.element coords) r.contributions;
            };
        in
        {
          diamond = check (runOn diamondGraph (mkAsymDef { }));
          o4 = check (runOn o4Graph (mkAsymDef { }));
        };
      expected = {
        diamond = {
          nEntries = 1;
          coords = [
            {
              producer = "top";
              ordinal = 0;
            }
          ];
          membershipHolds = true;
        };
        o4 = {
          nEntries = 2;
          coords = [
            {
              producer = "top";
              ordinal = 0;
            }
            {
              producer = "top";
              ordinal = 1;
            }
          ];
          membershipHolds = true;
        };
      };
    };
  };
}
