# ORACLE O1 — THE NAMED REFUSALS FIRE.
#
# Every required field of a view definition is omitted IN TURN, and each run must refuse. The
# sweep quantifies over the library's OWN published field enumeration, so a field added without a
# cell to omit it is impossible rather than merely unlikely.
#
# ★★ THIS FILE ASSERTS THAT A REFUSAL HAPPENED; `ci/tests-error.nix` ASSERTS WHAT IT SAID. The
# split is forced: the batch asserter behind `checks.default` forces every `expr`
# unconditionally, so a cell whose `expr` throws crashes that gate rather than failing it. A
# boolean over `tryEval` lives here; the message assertion — which is the half that makes the
# refusal NAMED rather than merely present — lives on the second output.
#
# ★★ THE POSITIVE CONTROL IS NOT OPTIONAL, AND THE MEASURED PRECEDENT SAYS WHY. In the grammar this
# library replaces, a misspelled channel silently yields `{ }` and the undeclared-channel check
# reads `false` EVEN UNDER `deepSeq`. A suite with no positive control cannot tell a refusal from
# an empty answer — which is exactly the failure it would be testing for.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;

  # One cell per required field, named after the field it omits.
  omissionCells = builtins.listToAttrs (
    map (field: {
      name = "test-omitting-${field}-refuses";
      value = {
        expr = refuses (v.viewDefinition (removeAttrs f.definitionArgs [ field ]));
        expected = true;
      };
    }) v.definitionFields
  );
in
{
  flake.tests.refusals = omissionCells // {
    # ── THE POSITIVE CONTROL, SAME RUN ──
    # The COMPLETE definition constructs, and the view it declares EVALUATES TO A RESULT. Both
    # halves matter: a definition that constructs and then materializes to nothing would satisfy a
    # construction-only control while reproducing the very failure this oracle exists to catch.
    test-control-the-complete-definition-constructs-and-materializes = {
      expr = {
        constructs = (builtins.tryEval (builtins.deepSeq (v.viewDefinition f.definitionArgs) true)).success;
        value = f.relation.value;
      };
      expected = {
        constructs = true;
        value = [ "inc" ];
      };
    };

    # ★ THE SWEEP QUANTIFIES OVER THE LIBRARY'S OWN ENUMERATION. If a thirteenth field appeared,
    # this list grows and a cell for it appears with it; if the enumeration were quietly emptied,
    # the sweep would be vacuous and this cell says so.
    test-control-the-field-enumeration-is-complete-and-non-trivial = {
      expr = v.definitionFields;
      expected = [
        "channel"
        "relation"
        "root"
        "direction"
        "admission"
        "order"
        "wellFormed"
        "distance"
        "tieSet"
        "empty"
        "combine"
        "dedup"
      ];
    };

    # ── k IS REQUIRED AND TOTAL, NEVER DEFAULTED ──
    # Called out beside the sweep because the measured defect it corrects is a DEFAULT and not an
    # omission: a shipped per-node default makes competition VACUOUS rather than absent, and a
    # carrier built on defaults inherits vacuity at the foundation. The fix is a mandatory key, so
    # both halves of the key refuse: the field itself, and the key function inside it.
    test-omitting-the-competition-key-function-refuses = {
      expr = refuses (v.dataOrder { channel = "settings"; });
      expected = true;
    };

    # ★ AND THE VACUITY IS SHOWN, so the requirement is not merely asserted. Under a PER-SCOPE key
    # every contribution is alone in its group and NOTHING IS EVER SHADOWED, while the gather-all
    # answer comes back whole; under the DECLARED key the same graph shadows two. That is exactly
    # the difference a default would have hidden, measured on one fixture in one run.
    test-a-per-scope-key-makes-competition-vacuous = {
      expr =
        let
          perScope = f.mkRelation {
            definition = v.viewDefinition (f.definitionArgs // { channel = f.perScopeKey; });
          };
        in
        {
          declaredShadowed = map (c: c.scope) f.relation.shadowed;
          declaredValue = f.relation.value;
          vacuousShadowed = map (c: c.scope) perScope.shadowed;
          vacuousValue = perScope.value;
        };
      expected = {
        declaredShadowed = [
          "mid"
          "root"
        ];
        declaredValue = [ "inc" ];
        vacuousShadowed = [ ];
        vacuousValue = [
          "inc"
          "mid"
          "root"
        ];
      };
    };

    # ── A READ AGAINST AN UNDECLARED NAME REFUSES BY NAME, AND NEVER YIELDS `{ }` ──
    test-an-undeclared-relation-refuses-rather-than-answering-empty = {
      expr = refuses (
        v.relationLookup {
          graph = f.graph;
          labeled = f.graph.labeled;
          scope = "inc";
          relation = "not-declared";
          wellFormed = f.admitAll;
        }
      );
      expected = true;
    };

    # THE CONTROL THAT DISTINGUISHES A REFUSAL FROM AN EMPTY ANSWER: a DECLARED relation with no
    # datums at the scope answers `[ ]` and does not refuse. Without this cell, "refuses on an
    # undeclared name" is consistent with a lookup that refuses on everything.
    test-control-a-declared-relation-with-no-datums-answers-empty-without-refusing = {
      expr = v.relationLookup {
        graph = f.graph;
        labeled = f.graph.labeled;
        scope = "inc";
        relation = "expose-in";
        wellFormed = f.admitAll;
      };
      expected = [ ];
    };

    # ── A FIELD NOBODY DECLARED IS REFUSED TOO, WHICH IS THE OTHER HALF OF TOTALITY ──
    # A misspelling would otherwise leave the real field missing AND leave the caller's intent
    # nowhere. This is also the arm that makes WIDENING UNSAYABLE at the materialization: there is
    # no field to put it in, and inventing one is refused by name.
    test-an-undeclared-field-is-refused-by-name = {
      expr = refuses (
        v.viewRelation {
          definition = f.definition;
          graph = f.graph;
          marks = f.noMarks;
          widen = _: true;
        }
      );
      expected = true;
    };

    # ── AN ALPHABET REFUSES THE RESERVED SYMBOLS ──
    # `$` marks the end of a path and `_` is the any-label wildcard of the expression grammar;
    # either as a letter would be unaddressable in every expression written over the alphabet.
    test-the-reserved-symbols-cannot-be-letters = {
      expr = {
        endOfPath = refuses (v.edgeLabels { letters = [ "$" ]; });
        wildcard = refuses (v.edgeLabels { letters = [ "_" ]; });
        control = (builtins.tryEval (v.edgeLabels { letters = [ "parent" ]; }).letters).success;
      };
      expected = {
        endOfPath = true;
        wildcard = true;
        control = true;
      };
    };

    # ── THE PATH EXPRESSION MAY NOT NAME CONTENT ──
    # A relation name in an admission expression would match nothing and say nothing: a silent
    # empty answer where a refusal belongs. This is what makes "a content name can never enter the
    # label word" true by construction rather than by discipline.
    test-an-expression-naming-a-relation-refuses = {
      expr = refuses (
        v.labelWellFormedness {
          alphabet = f.labels;
          expression = "import*";
        }
      );
      expected = true;
    };

    # ── THE LABEL ORDER IS TOTAL OVER THE ALPHABET ──
    # An unranked letter would otherwise take a default rank nobody declared — the shipped
    # behaviour this element exists to correct.
    test-an-unranked-letter-refuses = {
      expr = refuses (
        v.labelOrder {
          alphabet = f.labels;
          layers = [ [ "parent" ] ];
          endOfPath = -1;
        }
      );
      expected = true;
    };

    # ── THE SORTS ARE DISJOINT ──
    test-a-name-in-both-l-and-r-refuses-at-the-carrier = {
      expr = refuses (
        v.carrier {
          labels = f.labels;
          labelWellFormedness = f.admission;
          labelOrder = f.order;
          dataOrder = f.key;
          relations = v.relations {
            names = [
              "import"
              "parent"
            ];
          };
        }
      );
      expected = true;
    };

    # ══ THE MATERIALIZATION REFUSES AN UNKNOWN RELATION — IT DOES NOT ANSWER EMPTY ══
    #
    # ★★★ THE DEFECT THIS PINS, AND IT IS THIS LIBRARY'S OWN NAMED FAILURE MODE TURNED ON ITSELF.
    # The materialization reached the data component INLINE, bypassing the published
    # `relationLookup` — a private near-copy identical to it but for the refusal. So a MISSPELLED
    # relation and a DECLARED relation with no datums both answered `[ ]`, and no caller could tell
    # them apart. That is exactly the measured precedent `lib/refusal.nix` exists to forbid.
    #
    # The three rows of the table, in one cell: the control that answers, the declared-but-empty
    # that answers empty, and the undeclared that REFUSES.
    test-the-materialization-refuses-an-undeclared-relation = {
      expr = {
        # (a) CONTROL — a declared relation with datums materializes
        declaredWithDatums = f.relation.value;
        # (b) a DECLARED relation with no datums answers EMPTY and does not refuse. This is the row
        # that makes the refusal meaningful: without it, "refuses on an undeclared name" is
        # consistent with a materialization that refuses whenever it gathers nothing.
        declaredButEmpty =
          (f.mkRelation { definition = f.mkDefinition { relation = "expose-in"; }; }).value;
        declaredButEmptyRefuses = refuses (
          f.mkRelation { definition = f.mkDefinition { relation = "expose-in"; }; }
        );
        # (c) an UNDECLARED relation REFUSES
        undeclaredRefuses = refuses (
          f.mkRelation { definition = f.mkDefinition { relation = "not-a-relation"; }; }
        );
      };
      expected = {
        declaredWithDatums = [ "inc" ];
        declaredButEmpty = [ ];
        declaredButEmptyRefuses = false;
        undeclaredRefuses = true;
      };
    };

    # ★ AND THE REFUSAL COMES FROM THE PUBLISHED ELEMENT, NOT FROM A SECOND CHECK BOLTED ON. The
    # materialization's lookup and the raw `relationLookup` refuse the same name for the same
    # reason; a library carrying two refusal paths would have two messages to keep in step.
    test-control-the-published-lookup-refuses-the-same-name = {
      expr = refuses (
        v.relationLookup {
          graph = f.graph;
          labeled = f.graph.labeled;
          scope = "inc";
          relation = "not-a-relation";
          wellFormed = f.admitAll;
        }
      );
      expected = true;
    };
  };
}
