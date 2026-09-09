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

    # ── R§10.1, RIDER 1 — THE RETIREMENT RECORD SURVIVES ──
    # `lib/enumerations.nix` carries, immediately above `combines.setUnion`, the record of what
    # gen-resolve's retired `cascade` construct decided about its `acc` flag and what it only
    # declared — R§10.1 (a retirement names what it carries forward or it is a deletion). This
    # cell pins that the record SURVIVES, never that it is true; the flag-check behaviour it
    # describes is the existing cells above, cited there and not rewritten here (`den-hoag-p3y9`).
    #
    # ★ THE LIVE CONTROL IS THE SECOND ARM OF THIS SAME EXPR, not a second cell — a one-armed
    # `present = true` would still pass against a `match` that has stopped discriminating.
    # `absentControl` is a probe DERIVED from the file's own content (its sha256), not a literal
    # typed here: a hardcoded random string, once committed, is itself a published token that a
    # later sweep can quote back as a false live control (measured, `den-hoag-n3or2` — 52 such
    # forms already burned across 128 files in den-ag-design). A content hash is reproducible,
    # changes automatically if the file changes, and cannot occur as a literal substring of the
    # text it was hashed from.
    test-r10-1-rider-acc-value-domain-record-survives =
      let
        src = builtins.readFile ../../lib/enumerations.nix;
        absentToken = builtins.hashString "sha256" src;
      in
      {
        expr = {
          present = builtins.match ".*ANCHOR: R10\\.1-RIDER-ACC-VALUE-DOMAIN.*" src != null;
          absentControl = builtins.match ".*${absentToken}.*" src != null;
        };
        expected = {
          present = true;
          absentControl = false;
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
