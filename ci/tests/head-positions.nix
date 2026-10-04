# HEAD POSITIONS AND THE JOINED TRACE — ADR-0029's four-tier cases (den-hoag-zakjg, spec §6(iii) and
# §6(iv)), the values half. The refusals — a tail-placed head, a rank tie, a head letter the
# structure also steps, and each `innerOf` failure mode — are in `ci/tests-error.nix`, because their
# subject is a message.
#
# ★ The expected values are the spec's, evaluated at hub 9e9ac2a through the prototype
# (`zakjg-4tier-run-9e9ac2a-r3.tsv`), and here they come from the published units.
{
  genView,
  genScope,
  lib,
  ...
}:
let
  h = import ../head-positions-fixture.nix { inherit genView lib genScope; };
  g4 = k: {
    inherit (h.run { } k) moved received;
  };
  joinOf =
    k:
    let
      j = (h.run { } k).joined;
    in
    {
      joined = map (e: {
        inherit (e) contributor band;
        inner = {
          inherit (e.inner) priority winners;
        };
        word = e.entry.word;
      }) j.joined;
      unset = map (u: { inherit (u) scope reason priority; }) j.unset;
    };
  halves = j: {
    joined = map (e: e.contributor) j.joined;
    unset = map (r: r.scope) j.unset;
    unaccounted = map (r: r.scope) j.unaccounted;
  };
in
{
  flake.tests.head-positions = {
    # ── THE FOUR CASES AND THE SEED: the head letter decides first, structure only within one ──
    test-k1-both-set-the-more-specific-wins = {
      expr = g4 "k1";
      expected = {
        moved = [ "R" ];
        received = "R";
      };
    };
    test-k2-a-set-beats-a-default-across-structure = {
      expr = g4 "k2";
      expected = {
        moved = [ "T" ];
        received = "T";
      };
    };
    test-k3-a-default-beats-a-declared-default-only-contributor = {
      expr = g4 "k3";
      expected = {
        moved = [ "TD" ];
        received = "TD";
      };
    };
    test-k4-a-force-beats-a-set-across-structure = {
      expr = g4 "k4";
      expected = {
        moved = [ "TF" ];
        received = "TF";
      };
    };
    test-k5-nothing-moves-and-the-receiver-reads-its-own-default = {
      expr = g4 "k5";
      expected = {
        moved = [ ];
        received = "RD";
      };
    };
    test-k6-nothing-moves-and-the-receiver-reads-its-own-default = {
      expr = g4 "k6";
      expected = {
        moved = [ ];
        received = "RD";
      };
    };

    # The control that the cases read specificity: continuing beats stopping, and k1 flips.
    test-control-a-flipped-query-order-flips-k1 = {
      expr = {
        inherit (h.run { endOfPath = 1; } "k1") moved received;
      };
      expected = {
        moved = [ "T" ];
        received = "T";
      };
    };

    # ── WITHIN ONE HEAD, A STRUCTURAL TIE IS THE TIE SET'S ──
    test-a-within-head-tie-unions = {
      expr = h.tie (_: h.v.tieSets.union);
      expected = [
        "T"
        "U"
      ];
    };
    test-a-within-head-tie-folds-in-a-declared-position-order = {
      expr = h.tie (
        pos:
        h.v.tieSets.orderedFold {
          order = [
            (pos.position "u" "set")
            (pos.position "t" "set")
          ];
        }
      );
      expected = [
        "U"
        "T"
      ];
    };
    test-a-within-head-tie-refuses-under-refuse = {
      expr = (builtins.tryEval (builtins.deepSeq (h.tie (_: h.v.tieSets.refuse)) null)).success;
      expected = false;
    };

    # ── Q3: A RANK IN A VALUE IS DATA; THE SAME RANK ON A POSITION IS READ ──
    test-q3-a-marker-written-as-a-datum-is-not-read-by-the-door = {
      expr = h.q3InValue;
      expected = {
        moved = [ "R" ];
        received = "R";
        shadowed = [ "t" ];
        # control: the marker really reached the substrate, as data
        shadowedDatumTypes = [ "override" ];
      };
    };
    test-q3-the-same-rank-on-a-position-is-read = {
      expr = g4 "k4";
      expected = {
        moved = [ "TF" ];
        received = "TF";
      };
    };

    # ── THE CONSTRUCTION'S SHAPE: every word is one head letter, then structure ──
    test-every-word-starts-with-its-head-letter = {
      expr = map (k: map (e: e.word) (joinOf k).joined) [
        "k1"
        "k2"
        "k3"
        "k4"
      ];
      expected = [
        [ [ "set" ] ]
        [
          [
            "set"
            "tacks"
          ]
        ]
        [
          [
            "default"
            "tacks"
          ]
        ]
        [
          [
            "force"
            "tacks"
          ]
        ]
      ];
    };
    test-the-order-mark-ranks-each-head-alone-then-the-structure = {
      expr =
        let
          m = (h.run { } "k1").pos.orderMark;
        in
        {
          inherit (m) layers endOfPath;
        };
      expected = {
        layers = [
          [ "force" ]
          [ "set" ]
          [ "default" ]
          [ "tacks" ]
        ];
        endOfPath = 3;
      };
    };
    # The lifted admission is composed from the published WFL constructors, so it is a TERM, and
    # the calculus's parse of the spelled expression is the same term.
    test-the-admission-puts-the-head-alternation-first = {
      expr = (h.run { } "k1").pos.admission.term;
      expected =
        (genScope.wellFormed {
          alphabet = (h.run { } "k1").pos.admission.alphabet;
          expression = "(force|set|default)(tacks?)";
        }).term;
    };

    # ── THE JOIN: per surviving contribution, the contributor, its head letter and its own record ──
    test-join-k1-names-the-winning-definition-inside-the-contributor = {
      expr = (joinOf "k1").joined;
      expected = [
        {
          contributor = "r";
          band = "set";
          inner = {
            priority = 100;
            winners = [ "r.nix" ];
          };
          word = [ "set" ];
        }
      ];
    };
    test-join-k2 = {
      expr = map (e: { inherit (e) contributor band inner; }) (joinOf "k2").joined;
      expected = [
        {
          contributor = "t";
          band = "set";
          inner = {
            priority = 100;
            winners = [ "t.nix" ];
          };
        }
      ];
    };
    test-join-k3 = {
      expr = map (e: { inherit (e) contributor band inner; }) (joinOf "k3").joined;
      expected = [
        {
          contributor = "t";
          band = "default";
          inner = {
            priority = 1000;
            winners = [ "t.nix" ];
          };
        }
      ];
    };
    test-join-k4 = {
      expr = map (e: { inherit (e) contributor band inner; }) (joinOf "k4").joined;
      expected = [
        {
          contributor = "t";
          band = "force";
          inner = {
            priority = 50;
            winners = [ "t.nix" ];
          };
        }
      ];
    };
    # The control that the mis-keyed arm is a real mis-key: the two contributors' records differ in
    # exactly what the join reports, so a swapped join would change the answer, not repeat it. That
    # arm is refused by name (`tests-error.nix`, `joinedTrace` cells).
    test-control-the-swapped-records-carry-different-winners = {
      expr =
        map
          (
            k:
            let
              rs = (h.run { } k).rs;
            in
            [
              rs.r.winners or null
              rs.t.winners or null
            ]
          )
          [
            "k1"
            "k2"
            "k4"
          ];
      expected = [
        [
          [ "r.nix" ]
          [ "t.nix" ]
        ]
        [
          [ "r.nix" ]
          [ "t.nix" ]
        ]
        [
          [ "r.nix" ]
          [ "t.nix" ]
        ]
      ];
    };

    # ── NOTHING VANISHES: a moved value the relation never accounts for is recorded, not refused ──
    # k4: `t` moved under `force`. Each arm below removes `t`'s datum from the relation a different
    # way; its record lands in `unaccounted`, and in neither `joined` nor `unset`.
    test-a-moved-value-never-placed-is-unaccounted = {
      expr = halves (h.run { unplaced = [ "t" ]; } "k4").joined;
      expected = {
        joined = [ "r" ];
        unset = [ ];
        unaccounted = [ "t" ];
      };
    };
    test-a-relation-from-another-root-leaves-both-moved-values-unaccounted = {
      expr = halves (h.run { root = pos: pos.position "t" "force"; } "k4").joined;
      expected = {
        joined = [ ];
        unset = [ ];
        unaccounted = [
          "r"
          "t"
        ];
      };
    };
    test-a-datum-wellFormed-rejects-is-unaccounted-not-refused = {
      expr = halves (h.run { wellFormed = d: d != [ "TF" ]; } "k4").joined;
      expected = {
        joined = [ "r" ];
        unset = [ ];
        unaccounted = [ "t" ];
      };
    };
    # A boundary mark walling the out-edge of `t`'s position is a `withheld` row AT `t`, and it
    # witnesses no datum there: `t`'s rejected datum is still unaccounted, not hidden by the wall.
    test-a-mark-walling-a-dropped-contributors-edge-does-not-account-for-it = {
      expr = h.joinOver {
        edges.tacks =
          id:
          {
            r = [ "t" ];
            t = [ "u" ];
          }
          .${id} or [ ];
        expression = "tacks*";
        records = [
          (h.recordOf "r" [ "R" ])
          (h.recordOf "t" [ (lib.mkForce "TF") ])
          (h.recordOf "u" [ ])
        ];
        wellFormed = d: d != [ "TF" ];
        marks =
          pos: id:
          if id == pos.position "t" "force" then
            [
              {
                name = "wall";
                admits = _: false;
              }
            ]
          else
            [ ];
      };
      expected = {
        joined = [ "r" ];
        unset = [ "u" ];
        unaccounted = [ "t" ];
      };
    };
    # A contribution the dedup collapses is recorded in the relation's `dropped`, so it is
    # accounted for and does not land in `unaccounted`.
    test-a-dedup-collapsed-contribution-is-accounted = {
      expr = h.joinOver {
        edges.tacks =
          id:
          if id == "r" then
            [
              "t"
              "u"
            ]
          else
            [ ];
        expression = "tacks?";
        records = [
          (h.recordOf "r" [ ])
          (h.recordOf "t" [ "X" ])
          (h.recordOf "u" [ "X" ])
        ];
        dedup = h.v.dedups.byDatum;
      };
      expected = {
        joined = [ "t" ];
        unset = [ "r" ];
        unaccounted = [ ];
      };
    };
    test-control-the-same-case-unaltered-accounts-for-both = {
      expr = halves (h.run { } "k4").joined;
      expected = {
        joined = [ "t" ];
        unset = [ ];
        unaccounted = [ ];
      };
    };

    # ── NOTHING VANISHES: a field that did not move is recorded, and the substrate does not ──
    test-join-k3-records-the-root-as-default-only-and-the-substrate-does-not-mention-it = {
      expr =
        let
          r = h.run { } "k3";
        in
        {
          inherit (joinOf "k3") unset;
          inherit (r) substrateMentions;
        };
      expected = {
        unset = [
          {
            scope = "r";
            reason = "unset: default-only";
            priority = 1500;
          }
        ];
        # control: the same predicate over the contributor that did move
        substrateMentions = {
          r = false;
          t = true;
        };
      };
    };
    test-join-k6-records-both-as-default-only = {
      expr = {
        inherit (joinOf "k6") joined unset;
      };
      expected = {
        joined = [ ];
        unset = [
          {
            scope = "r";
            reason = "unset: default-only";
            priority = 1500;
          }
          {
            scope = "t";
            reason = "unset: default-only";
            priority = 1500;
          }
        ];
      };
    };
  };
}
