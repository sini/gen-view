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
{ genView, genScope, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  r = import ../reference-fixture.nix { inherit genView genScope; };
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

  # The same sweep for the reference construct, over ITS published enumeration. Two sweeps rather
  # than one parameterised helper: the two constructs have different field sets for different
  # reasons, and a shared generator would invite a later reader to assume one enumeration covers
  # both when only the list differs.
  referenceOmissionCells = builtins.listToAttrs (
    map (field: {
      name = "test-omitting-reference-${field}-refuses";
      value = {
        expr = refuses (v.referenceResolution (removeAttrs r.referenceArgs [ field ]));
        expected = true;
      };
    }) v.referenceResolutionFields
  );
in
{
  flake.tests.refusals =
    omissionCells
    // referenceOmissionCells
    // {
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
            scope = "inc";
            relation = "not-a-relation";
            wellFormed = f.admitAll;
          }
        );
        expected = true;
      };

      # ══ REFERENCE RESOLUTION — THE SAME DISCIPLINE, ON A CONSTRUCT WHOSE FIELDS WERE DEFAULTS ══
      #
      # ★★★ WHAT THIS SWEEP DISCHARGES IS A MEASURED DEFECT AND NOT A HYPOTHETICAL. The wrapper this
      # construct succeeds rode on FOUR silent defaults: a direction field defaulted to one arm, and
      # the two shadowing flags and the transitive-import closure left to the authority's own
      # defaults — so the D < I < P discipline and the import closure were decided somewhere the
      # declaration could not be read. Required-and-total is what makes the declaration determine its
      # own defining query, and this sweep is what makes "required" a checked word.

      # ★ THE ENUMERATION IS THE SWEEP'S QUANTIFIER, so it is pinned here for the same reason the
      # definition's is: if it were quietly emptied, the sweep above would be VACUOUS and every
      # omission cell would vanish with nothing going red.
      test-control-the-reference-field-enumeration-is-complete-and-non-trivial = {
        expr = v.referenceResolutionFields;
        expected = [
          "engine"
          "name"
          "wellFormed"
          "project"
          "localShadowsImport"
          "importShadowsParent"
          "transitiveImports"
        ];
      };

      # ── THE POSITIVE CONTROL, SAME RUN ──
      # The COMPLETE declaration constructs AND ITS COMPUTE RESOLVES. Both halves matter for exactly
      # the reason the definition's control states: a construct that built and then answered nothing
      # would satisfy a construction-only control while reproducing the failure this oracle exists to
      # catch. The value asserted is the one the live consumer's declaration produces — the
      # provider's capability tags, reached from a requirer that provides nothing itself.
      test-control-the-complete-reference-declaration-constructs-and-resolves = {
        expr = {
          constructs =
            (builtins.tryEval (builtins.deepSeq (v.referenceResolution r.referenceArgs) true)).success;
          value = r.providesSelf.get "req" "resolved";
        };
        expected = {
          constructs = true;
          value = [
            "read"
            "write"
          ];
        };
      };

      # ── THE FIELD SET IS CLOSED, WHICH IS THE OTHER SIDE OF TOTALITY ──
      test-an-undeclared-reference-field-is-refused = {
        expr = refuses (v.referenceResolution (r.referenceArgs // { codomain = "atMostOne"; }));
        expected = true;
      };

      # ── THE INJECTED AUTHORITY IS CHECKED AT CONSTRUCTION, NOT AT SOME LATER FORCE ──
      # A value publishing no `query` is the whole of "wrong authority", and catching it here is what
      # keeps the failure at the declaration rather than inside an evaluator three layers away.
      test-an-engine-publishing-no-query-refuses = {
        expr = {
          noQuery = refuses (v.referenceResolution (r.referenceArgs // { engine = { }; }));
          notAnAttrset = refuses (v.referenceResolution (r.referenceArgs // { engine = "gen-scope"; }));
        };
        expected = {
          noQuery = true;
          notAnAttrset = true;
        };
      };

      # ── THE REMAINING FIELD SHAPES, EACH REFUSED BY NAME ──
      # One cell rather than five, because the claim is one claim: every field is checked for the
      # shape its role requires, and a field that took anything would be a field the declaration does
      # not really declare.
      test-a-reference-field-of-the-wrong-shape-refuses = {
        expr = {
          emptyName = refuses (v.referenceResolution (r.referenceArgs // { name = ""; }));
          nonStringName = refuses (v.referenceResolution (r.referenceArgs // { name = 7; }));
          nonFunctionWellFormed = refuses (v.referenceResolution (r.referenceArgs // { wellFormed = true; }));
          nonFunctionProject = refuses (v.referenceResolution (r.referenceArgs // { project = [ ]; }));
          nonBoolLocalShadowsImport = refuses (
            v.referenceResolution (r.referenceArgs // { localShadowsImport = "yes"; })
          );
          nonBoolImportShadowsParent = refuses (
            v.referenceResolution (r.referenceArgs // { importShadowsParent = null; })
          );
          nonBoolTransitiveImports = refuses (
            v.referenceResolution (r.referenceArgs // { transitiveImports = 0; })
          );
        };
        expected = {
          emptyName = true;
          nonStringName = true;
          nonFunctionWellFormed = true;
          nonFunctionProject = true;
          nonBoolLocalShadowsImport = true;
          nonBoolImportShadowsParent = true;
          nonBoolTransitiveImports = true;
        };
      };

      # ══ ORACLE O2 — THE NULL-PROJECTION REFUSAL, WITH ITS VACUITY CHECK AND ITS BOUND ══
      #
      # ★★★ THE ONE REFUSAL THAT FIRES AT MATERIALIZATION, AND THE THIRD DEFECT OF THE FUSED
      # PREDICATE CLOSED. The wrapper this construct succeeds used `null` for BOTH "not a binding
      # here" AND "the value", so a datum whose projection was legitimately null was indistinguishable
      # from an absent binding and vanished with nothing saying so. Split into two operators the case
      # becomes SAYABLE — a node the predicate ADMITS whose projection is null — and once it is
      # sayable it is refused, because the authority reads that null as an absence.
      #
      # ★★ THE FOUR ROWS ARE ONE CLAIM AND MUST BE READ TOGETHER:
      #   (a) SUBJECT   — an admitted node with a null projection REFUSES.
      #   (b) POSITIVE  — the same fixture, same declaration, non-null projection: it resolves.
      #   (c) VACUITY   — the same composition WITH THE GUARD REMOVED answers `null`. This is what
      #       makes (a) a statement about the guard: without it, (a) is consistent with a fixture
      #       that refuses for some reason of its own.
      #   (d) REACHABILITY — the guard-removed composition at a NON-null projection answers the
      #       holder's datum. Row (c) on its own is worth nothing, because an UNREACHED node answers
      #       null too; this row is what makes (c)'s null the projection's.
      #
      # ★ AND THE REFUSAL IS BOUNDED — see the cell below. It must NOT fire on a node the predicate
      # declines, which is an ordinary absence and stays one.
      test-a-null-projection-at-an-admitted-node-refuses = {
        expr = {
          subjectRefuses = refuses (r.projectionSelf.get "reader" "nullArm");
          positive = r.projectionSelf.get "reader" "tagArm";
          unguarded = r.projectionSelf.get "reader" "unguardedNullArm";
          unguardedReaches = r.projectionSelf.get "reader" "unguardedTagArm";
        };
        expected = {
          subjectRefuses = true;
          positive = "present";
          unguarded = null;
          unguardedReaches = "present";
        };
      };

      # ★★ THE BOUND, AND IT IS THE HALF THAT KEEPS THE CHANGE HONEST. `lonely` includes `blank`,
      # which the predicate DECLINES — so nothing is admitted, the projection never runs, and the
      # answer is the authority's ordinary "no visible binding". An empty answer is never a refusal
      # in this library; what the cell above adds is the converse, that a refusal must never arrive
      # wearing the shape of an empty answer. A guard that fired here would have converted every
      # ordinary absence into an error.
      test-control-an-unadmitted-node-is-an-ordinary-absence-and-does-not-refuse = {
        expr = {
          refuses = refuses (r.projectionSelf.get "lonely" "nullArm");
          value = r.projectionSelf.get "lonely" "nullArm";
        };
        expected = {
          refuses = false;
          value = null;
        };
      };
    };
}
