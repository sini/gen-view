# THE MOVEMENT ORACLE — the movement spec's §9.3 confirmation (O2, O3) and §9.4's collision probe,
# over gen-view's own trace, with every control collected.
#
# AC-7 ran these on 2026-08-20 against the frozen edge instrument (spec §9.5 records the verdict).
# They live here as the meter for `viewRelation` and `tieSets`: O2's permutation invariance and O3's
# content blindness are the halves spec §9.5 keeps "with full theory backing", and both are
# properties of the destination's `trace`/`hashTrace`, so that is what they read.
#
# ★ NOT HERE, EACH WITH ITS REASON.
#   · O1, the totality of the map into the edge record, and the two sitting questions measured
#     across it (kind vs relation, placement arity): the edge record's library retired (ADR-0010 §3)
#     and §9.5 ruled both questions (kind = relation ratified; the single-placement bound accepted).
#   · Arm (d) on a TWO-survivor base under `union`: with a non-commutative combine its value is walk
#     order, and whether that construction answers or refuses is `den-hoag-nq9p`'s open ruling (Q1).
#     Arm (d)'s ONE-survivor reading stays below (`test-o2-d-different-tieSet-does-NOT-move-the-hash`),
#     where no disposition can reorder anything. The two-survivor axis IS read below too, but by
#     comparing `orderedFold` against `orderedFold` — never against `union` — which carries no
#     dependency on Q1's verdict (`reports/den-hoag-ff2uo-wtac7-recover-v0.md`). LEFT OUT: the third
#     cell of that triad, which read `orderedFold` declared in the WALK's own order AGAINST `union`'s
#     baseline, to isolate "declaring a different order" from "naming a tie-set at all" — that
#     isolation is stated only in terms of `union`'s own two-survivor value, so it has no Q1-free
#     re-expression and re-enters once Q1 is read.
#
# ★ EVERY CONTROL CELL IS NAMED `test-control-*`. NO CELL ASSERTS A THROW BY LETTING `expr` THROW:
# expected refusals are measured through `builtins.tryEval`, so `expr` is always a forcible value.
{ genView, ... }:
let
  fixture = import ../fixture.nix { inherit genView; };
  corpus = import ./_movement-oracle/corpus.nix { inherit genView; };
  o2 = import ./_movement-oracle/o2.nix { inherit genView fixture; };
  o3 = import ./_movement-oracle/o3.nix { inherit genView fixture corpus; };
  o94 = import ./_movement-oracle/o94.nix { inherit genView fixture; };
  c = corpus;
in
{
  flake.tests.movement-oracle = {

    # ── O2 — SENSITIVITY ────────────────────────────────────────────────────────────────────────
    test-o2-a-changed-WFL-moves-the-hash = {
      expr = o2.verdict.a_changed_WFL.differsFromBase;
      expected = true;
    };

    test-o2-b-changed-admission-domain-moves-the-hash = {
      expr = o2.verdict.b_changed_admission_domain.differsFromBase;
      expected = true;
    };

    test-o2-c-different-competition-key-moves-the-hash = {
      expr = o2.verdict.c_different_competition_key.differsFromBase;
      expected = true;
    };

    test-o2-e-boundary-mark-added-moves-the-hash = {
      expr = o2.verdict.e_boundary_mark_added.differsFromBase;
      expected = true;
    };

    # ★ THE INSTRUMENT'S DECLARED LIMIT, NOT A MISS (spec §9.5 restates arm (d) against the pair):
    # `trace` is a function of the entry SET and a disposition never changes the surviving set, so
    # this axis cannot move the fingerprint without breaking the permutation control below.
    test-o2-d-different-tieSet-does-NOT-move-the-hash = {
      expr = o2.verdict.d_different_tieSet.differsFromBase;
      expected = false;
    };

    # ── ARM (d), THE TWO-SURVIVOR AXIS, Q1-INDEPENDENT ──────────────────────────────────────────
    # Two `orderedFold` DECLARATIONS, never `orderedFold` against `union`: the flat-order base's
    # two-member surviving group is disposed by a declared order that names the scopes in the
    # WALK's own order, and again by one that reverses the first two. `trace` is a function of the
    # entry SET (as above), so the disposition still cannot move the fingerprint; `combine`
    # (`listAppend`) is order-sensitive, so it still moves the answer.
    test-o2-d-mechanism-orderedFold-order-moves-the-answer-not-the-hash = {
      expr = {
        answersDiffer =
          o2.tieSetRerun.flat_orderedFold_walkOrder.answer != o2.tieSetRerun.flat_orderedFold_reversed.answer;
        hashesEqual =
          o2.tieSetRerun.flat_orderedFold_walkOrder.hash == o2.tieSetRerun.flat_orderedFold_reversed.hash;
      };
      expected = {
        answersDiffer = true;
        hashesEqual = true;
      };
    };

    test-control-o2-a-pure-permutation-leaves-the-hash-byte-equal = {
      expr = o2.control.byteEqual;
      expected = true;
    };

    # THE CONTROL'S OWN CONTROL: the permutation has to be a real one, or byte-equality is a
    # measurement of nothing.
    test-control-o2-the-permutation-is-a-real-permutation = {
      expr = {
        inherit (o2.control) permutationIsReal scopePermutationIsReal;
      };
      expected = {
        permutationIsReal = true;
        scopePermutationIsReal = true;
      };
    };

    # ── O2, THE SECOND HALF OF THE PAIR — the MATERIALIZED CHANNEL VALUE ────────────────────────
    # R§9.2's acceptance oracle is ⟨`hashTrace` over the mapped topology, the materialized channel
    # value⟩. The cells above measure the FIRST half's sensitivity; these measure the SECOND on the
    # SAME topology pairs, so every arm reports both.
    test-o2-value-half-abce-all-differ = {
      expr = builtins.map (n: o2.valueVerdict.${n}) [
        "a_changed_WFL"
        "b_changed_admission_domain"
        "c_different_competition_key"
        "e_boundary_mark_added"
      ];
      expected = [
        "differs"
        "differs"
        "differs"
        "differs"
      ];
    };

    # On the BASE topology the surviving set has ONE member, so the tie-set axis moves NEITHER half.
    test-o2-value-half-d-is-byte-equal-on-the-base = {
      expr = o2.valueVerdict.d_different_tieSet;
      expected = "byte-equal";
    };

    # The value half of the Q1-independent re-run: the SAME `orderedFold`-vs-`orderedFold` pair the
    # mechanism cell above reads, showing the value half catches the axis the hash half is blind to.
    test-o2-value-half-catches-the-orderedFold-order-axis-the-hash-cannot = {
      expr = {
        value = o2.tieSetRerunValues.orderedFoldWalkOrder_vs_reversed;
        hashEqual =
          o2.tieSetRerun.flat_orderedFold_walkOrder.hash == o2.tieSetRerun.flat_orderedFold_reversed.hash;
      };
      expected = {
        value = "differs";
        hashEqual = true;
      };
    };

    # ★ ALL THREE OUTCOMES OF THE VALUE COMPARISON MUST BE LIVE, or the column is two-valued in
    # disguise and a declaration that REFUSED would be reported as agreement.
    test-control-o2-the-value-comparison-has-all-three-outcomes-live = {
      expr = o2.valueControls;
      expected = {
        knownDifferent = "differs";
        knownEqual = "byte-equal";
        knownRefusing = "not-evaluable";
      };
    };

    # The permutation control on the SECOND half, measured in the same run as the first half's.
    test-control-o2-a-pure-permutation-leaves-the-value-byte-equal = {
      expr = o2.control.valueComparison;
      expected = "byte-equal";
    };

    # ── O3 — CONTENT BLINDNESS ──────────────────────────────────────────────────────────────────
    test-o3-different-content-same-topology-is-byte-equal = {
      expr = o3.byteEqual;
      expected = true;
    };

    test-control-o3-the-two-runs-answer-differently = {
      expr = o3.control.answersDiffer;
      expected = true;
    };

    test-control-o3-the-two-runs-have-identical-structural-topology = {
      expr = o3.control.contributionsOne == o3.control.contributionsTwo;
      expected = true;
    };

    test-o3-the-trace-does-not-force-the-datum = {
      expr = {
        inherit (o3.unforced) hashSucceeded;
      };
      expected = {
        hashSucceeded = true;
      };
    };

    test-control-o3-the-answer-does-force-the-datum = {
      expr = o3.unforced.answerSucceeded;
      expected = false;
    };

    test-o3-v1-arms-A-and-E-hash-alike-and-answer-differently = {
      expr = {
        inherit (o3.armsAE) byteEqual answersDiffer;
      };
      expected = {
        byteEqual = true;
        answersDiffer = true;
      };
    };

    # ── §9.4 — THE COLLISION PROBE ──────────────────────────────────────────────────────────────
    # The key-encoding landing made the key injective, so the pair §9.4 collided keys apart here.
    test-94-destination-the-key-no-longer-collides = {
      expr = o94.destination.keysCollide;
      expected = false;
    };

    test-94-destination-the-oracle-still-separates = {
      expr = {
        inherit (o94.destination) entriesSeparate hashesSeparate;
      };
      expected = {
        entriesSeparate = true;
        hashesSeparate = true;
      };
    };

    test-control-94-destination-two-ordinary-entries-get-distinct-keys = {
      expr = o94.destination.control.ordinaryKeysDiffer;
      expected = true;
    };

    test-94-destination-permutation-invariance-holds = {
      expr = o94.destination.permutation.byteEqual;
      expected = true;
    };

    # ── THE CORPUS — the v1 arms re-expressed ───────────────────────────────────────────────────
    test-v1-arm-A-reproduces-its-recorded-answer = {
      expr = c.arms.A.result.value;
      expected = [ "H-val" ];
    };

    test-v1-arm-C-reproduces-its-recorded-answer = {
      expr = c.arms.C.result.value;
      expected = [ "F-val" ];
    };

    test-v1-arm-E-reproduces-its-recorded-answer = {
      expr = c.arms.E.result.value;
      expected = [ "S-exposed" ];
    };

    # ARM E IS ARM C's CONTROL AND MUST BEHAVE LIKE ONE: flipping exactly one datum's relation at `H`
    # must flip the answer, or arm C's result is not caused by what the record says causes it.
    test-control-v1-arm-C-and-arm-E-answer-differently = {
      expr = c.arms.C.result.value != c.arms.E.result.value;
      expected = true;
    };

    test-v1-arms-B-D-F-are-not-expressible-as-one-declaration = {
      expr = builtins.map (n: c.arms.${n}.expressible) [
        "B"
        "D"
        "F"
      ];
      expected = [
        false
        false
        false
      ];
    };
  };
}
