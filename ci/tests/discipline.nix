# ORACLE O2 — TIE-SET AND COMBINE DISCIPLINE HOLD AT CONSTRUCTION.
#
# Five arms, each of which must REFUSE, and five lawful counterparts in the same run, each of which
# must CONSTRUCT. The pairing is the whole instrument: five refusals with no counterparts are
# equally consistent with a constructor that refuses everything.
#
# ★ ALL FIVE REDUCE TO ONE QUESTION ASKED AT CONSTRUCTION, and that is the design rather than a
# coincidence. An unapplied `tieSets.orderedFold` is a FUNCTION, an unapplied `combines.setUnion` is
# a FUNCTION, and a hand-written attrset carries no element tag — so "outside the three", "no
# declared order", "no declared ACC flag" and "outside the whitelist" are all the tag check, and
# the fifth (arrival order) is the one arm that needs a check of its own because its subject is a
# value that is genuinely there.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;
  constructs = thunk: (builtins.tryEval (builtins.deepSeq thunk true)).success;
  withField = overrides: v.viewDefinition (f.definitionArgs // overrides);
in
{
  flake.tests.discipline = {
    # ── ARM 1 — `tieSet` OUTSIDE THE THREE ──
    test-a-tieset-outside-the-three-refuses = {
      expr = refuses (withField {
        tieSet = {
          arm = "strongest-wins";
          order = null;
        };
      });
      expected = true;
    };
    test-control-each-of-the-three-lawful-tiesets-constructs = {
      expr =
        map
          (
            t:
            constructs (withField {
              tieSet = t;
            })
          )
          [
            v.tieSets.union
            v.tieSets.refuse
            (v.tieSets.orderedFold {
              order = [
                "inc"
                "mid"
                "root"
              ];
            })
          ];
      expected = [
        true
        true
        true
      ];
    };

    # ── ARM 2 — `orderedFold` WITH NO DECLARED ORDER ──
    # The unapplied arm is a function, and a function is not a tie-set element.
    test-an-orderedfold-with-no-declared-order-refuses = {
      expr = refuses (withField {
        tieSet = v.tieSets.orderedFold;
      });
      expected = true;
    };

    # ── ARM 3 — `orderedFold` WHOSE ORDER IS ARRIVAL ORDER ──
    # ★ `order = null` IS ARRIVAL ORDER'S SPELLING, and it is the shape a declaration migrating
    # from a grammar with no declared order actually arrives in. The tempting reading of "nothing"
    # is "the order they arrived in", under which the ordered-fold ruling and the
    # presentation-invariance ruling collide head-on — so the absence is refused rather than
    # interpreted.
    test-an-orderedfold-over-arrival-order-refuses = {
      expr = refuses (v.tieSets.orderedFold { order = null; });
      expected = true;
    };
    # And the empty declared order refuses too: an ordered fold that disposes its surviving set by
    # nothing is not a disposition.
    test-an-orderedfold-over-an-empty-order-refuses = {
      expr = refuses (v.tieSets.orderedFold { order = [ ]; });
      expected = true;
    };

    # ── ARM 4 — `combine` OUTSIDE THE WHITELIST ──
    # An arbitrary caller-supplied function is NOT admissible: the ascending chain condition is
    # undecidable from one, so it is a declared carrier property and not an inferred one.
    test-an-arbitrary-combine-function-refuses = {
      expr = refuses (withField {
        combine = a: b: a ++ b;
      });
      expected = true;
    };
    test-a-hand-written-combine-record-refuses = {
      expr = refuses (withField {
        combine = {
          arm = "listAppend";
          op = a: b: a ++ b;
          unit = [ ];
          associative = true;
          setSemilattice = false;
          acc = null;
        };
      });
      expected = true;
    };
    test-control-each-whitelisted-combine-constructs-with-its-own-unit = {
      expr =
        map
          (
            c:
            constructs (withField {
              combine = c.combine;
              empty = c.empty;
            })
          )
          [
            {
              combine = v.combines.listAppend;
              empty = [ ];
            }
            {
              combine = v.combines.attrsShallow;
              empty = { };
            }
            {
              combine = v.combines.setUnion { acc = true; };
              empty = [ ];
            }
          ];
      expected = [
        true
        true
        true
      ];
    };

    # ── ARM 5 — A SET-SEMILATTICE COMBINE WITH NO DECLARED ACC FLAG ──
    test-a-set-semilattice-combine-without-its-acc-flag-refuses = {
      expr = refuses (withField {
        combine = v.combines.setUnion;
      });
      expected = true;
    };
    test-a-non-boolean-acc-flag-refuses = {
      expr = refuses (v.combines.setUnion { acc = "yes"; });
      expected = true;
    };
    # ★ AND THE FLAG IS CARRIED, not merely demanded: a declaration that answered the question and
    # then dropped the answer would satisfy the refusal above while leaving the property
    # unreachable to anything downstream.
    test-control-the-acc-flag-is-carried-on-the-constructed-combine = {
      expr = {
        declaredTrue = (v.combines.setUnion { acc = true; }).acc;
        declaredFalse = (v.combines.setUnion { acc = false; }).acc;
        nonSemilattice = v.combines.listAppend.setSemilattice;
      };
      expected = {
        declaredTrue = true;
        declaredFalse = false;
        nonSemilattice = false;
      };
    };

    # ── THE UNIT CROSS-CHECK ──
    # A fold whose seed is not its operation's unit is not the fold it declares, and the mismatch
    # is silent in every answer it gives.
    test-an-empty-that-is-not-the-combines-unit-refuses = {
      expr = refuses (withField {
        combine = v.combines.attrsShallow;
        empty = [ ];
      });
      expected = true;
    };

    # ── THE DEDUP POLICY IS REQUIRED AND CLOSED ──
    test-a-dedup-outside-the-arms-refuses = {
      expr = refuses (withField {
        dedup = {
          arm = "by-vibes";
          keyOf = null;
        };
      });
      expected = true;
    };
    test-control-each-declared-dedup-arm-constructs = {
      expr =
        map
          (
            d:
            constructs (withField {
              dedup = d;
            })
          )
          [
            v.dedups.none
            v.dedups.byDatum
            (v.dedups.byKey { keyOf = c: c.scope; })
          ];
      expected = [
        true
        true
        true
      ];
    };

    # ── DIRECTION IS A CLOSED ENUMERATION ──
    test-an-undeclared-direction-refuses = {
      expr = refuses (withField {
        direction = "sideways";
      });
      expected = true;
    };
    test-control-both-declared-directions-construct = {
      expr = map (
        d:
        constructs (withField {
          direction = d;
        })
      ) v.directions;
      expected = [
        true
        true
      ];
    };

    # ── THE ARMS ARE THE PUBLISHED ENUMERATIONS, SO THE SWEEPS ABOVE CANNOT GO STALE ──
    test-control-the-published-arm-enumerations = {
      expr = {
        tieSets = v.tieSetArms;
        combines = v.combineArms;
        dedups = v.dedupArms;
        directions = v.directions;
      };
      expected = {
        tieSets = [
          "union"
          "refuse"
          "orderedFold"
        ];
        combines = [
          "listAppend"
          "attrsShallow"
          "setUnion"
        ];
        dedups = [
          "none"
          "byDatum"
          "byKey"
        ];
        directions = [
          "outbound"
          "inbound"
        ];
      };
    };
  };
}
