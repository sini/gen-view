# ORACLE O6 — NARROWING ONLY, AND THE MARK IS NAMED.
#
# Two claims:
#   (i)  no expression reaches an effective E WIDER than a node's mark — a definition attempting it
#        does not construct;
#   (ii) a query narrowed against a marked node yields a diagnostic NAMING THE MARK.
#
# ★★ (i) IS NOT ENFORCED BY A CHECK, AND THAT IS THE STRONGER FORM. Effective E = NODE MARKS ∩
# DECLARED ADMISSION, and the marks are applied AT THE ACCESSOR, so the construction only ever
# REMOVES edges from what the underlying accessor offers. WIDENING IS NOT FORBIDDEN — IT IS
# UNSAYABLE: intersection has no inverse the author can reach, and there is no global dial to
# disagree with the derivation because the mark IS an input to it. The cells below measure both
# halves of that: there is no field to widen through, and the strongest mark a caller can write
# still cannot add an edge.
#
# ★★ AND (ii) EXISTS BECAUSE SILENCE MUST NEVER BECOME ACCESS. An accessor that filtered and said
# nothing would answer a narrowed query with a short answer and no way to tell a boundary from an
# absent edge. The two are indistinguishable in the ANSWER and must not be indistinguishable in the
# DIAGNOSTIC — so the withheld set travels INSIDE the materialized result rather than beside it,
# because a side channel a consumer may ignore is exactly the fail-open shape a boundary rule
# cannot afford.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  refuses = thunk: !(builtins.tryEval (builtins.deepSeq thunk true)).success;

  unmarked = f.relation;
  marked = f.mkRelation { marks = f.includeMark; };
  admitAll = f.mkRelation { marks = f.admitAllMark; };
in
{
  flake.tests.bounds = {
    # ── (i) THERE IS NO FIELD TO WIDEN THROUGH ──
    # The materialization's field set is closed, so a caller reaching for a widening dial is
    # refused by name rather than quietly ignored.
    test-a-widening-field-does-not-construct = {
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

    # ── (i) THE STRONGEST MARK A CALLER CAN WRITE STILL CANNOT ADD AN EDGE ──
    # A mark admitting EVERY label yields exactly the unmarked answer and never more, because the
    # construction subtracts and has no term that adds.
    test-a-mark-that-admits-everything-cannot-widen-the-answer = {
      expr = {
        same = map (c: c.scope) admitAll.contributions == map (c: c.scope) unmarked.contributions;
        noDiagnostic = admitAll.withheld;
      };
      expected = {
        same = true;
        noDiagnostic = [ ];
      };
    };

    # ── (ii) THE DIAGNOSTIC NAMES THE MARK ──
    # `no-containment` refuses the containment letter at `leaf`, so the containment reach is gone
    # from the answer AND the withheld entry says which mark did it, on which edge.
    test-a-narrowed-query-names-the-mark-that-narrowed-it = {
      expr = {
        visible = map (c: c.scope) marked.contributions;
        withheld = marked.withheld;
      };
      expected = {
        visible = [ "mid" ];
        withheld = [
          {
            scope = "leaf";
            label = "include";
            target = "inc";
            marks = [ "no-containment" ];
          }
        ];
      };
    };

    # ★ THE CONTROL, SAME RUN, SAME FIXTURE: the UNMARKED equivalent yields NO diagnostic and the
    # FULL answer. Without it, "a marked query is short and names a mark" is consistent with a
    # query that is short for some other reason and names a mark that withheld nothing.
    test-control-the-unmarked-equivalent-has-no-diagnostic-and-the-full-answer = {
      expr = {
        visible = map (c: c.scope) unmarked.contributions;
        shadowed = map (c: c.scope) unmarked.shadowed;
        withheld = unmarked.withheld;
      };
      expected = {
        visible = [ "inc" ];
        shadowed = [
          "mid"
          "root"
        ];
        withheld = [ ];
      };
    };

    # ── THE MARK NARROWS AN EDGE THE DECLARED ADMISSION ALLOWS ──
    # This is what makes the effective policy an INTERSECTION rather than a second spelling of the
    # declaration: the expression `(parent|include)*` admits the containment letter, and the mark
    # removes it anyway.
    test-the-effective-policy-is-the-intersection-not-the-declaration = {
      expr = {
        declarationAdmitsTheLetter = builtins.elem "include" f.definition.admission.literals;
        andYetTheEdgeIsGone = builtins.filter (c: c.scope == "inc") marked.contributions == [ ];
      };
      expected = {
        declarationAdmitsTheLetter = true;
        andYetTheEdgeIsGone = true;
      };
    };

    # ── THE DIAGNOSTIC CARRIES THE FULL WITHHELD SET AND TRAVELS INSIDE THE RESULT ──
    # Not a function to call and not a companion value beside the answer: a consumer holding the
    # result holds the diagnostic, and cannot hold one without the other.
    test-the-diagnostic-is-plain-data-inside-the-result = {
      expr = {
        isList = builtins.isList marked.withheld;
        keys = builtins.attrNames (builtins.head marked.withheld);
      };
      expected = {
        isList = true;
        keys = [
          "label"
          "marks"
          "scope"
          "target"
        ];
      };
    };

    # ── AN EDGE WITHHELD BY SEVERAL MARKS IS ONE ENTRY NAMING ALL OF THEM ──
    # Picking one would make the report depend on mark order; reporting the edge once per mark
    # would make the withheld set uncountable as a set of edges.
    test-several-marks-on-one-edge-produce-one-entry-naming-all = {
      expr =
        (f.mkRelation {
          marks =
            id:
            if id == "leaf" then
              [
                {
                  name = "no-containment";
                  admits = l: l != "include";
                }
                {
                  name = "ancestors-only";
                  admits = l: l == "parent";
                }
              ]
            else
              [ ];
        }).withheld;
      expected = [
        {
          scope = "leaf";
          label = "include";
          target = "inc";
          marks = [
            "no-containment"
            "ancestors-only"
          ];
        }
      ];
    };
  };
}
