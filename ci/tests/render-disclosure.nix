# ── A RENDERING DISCLOSES BY TYPE; IT NEVER COERCES AND NEVER ABORTS (den-hoag-g1qy0) ──
# `renderEntry` is published over any entry, and a hand-built one may carry anything in any field.
# Each leaf renders by `builtins.typeOf`: a string, a number and a path as values, every other type
# as its marker. Before the split an `outPath`/`__toString` set rendered as the string it coerces
# to, and a function or a plain set aborted past `tryEval`, taking the whole `renderTrace` with it.
# The sort key is the other half of the split and refuses the same entries by name
# (`ci/tests-error.nix`, `entry-refusals`).
{ genView, genScope, ... }:
let
  v = genView;
  f = import ../fixture.nix { inherit genView genScope; };
  e0 = v.traceEntryOf {
    contribution = builtins.head f.relation.contributions;
    inherit (f) placement;
  };
  # The rendering with the source scope replaced — the leaf a derivation standing for a scope name
  # reaches. The genuine scope is `"inc"`.
  withScope =
    scope:
    v.renderEntry (
      e0
      // {
        source = e0.source // {
          inherit scope;
        };
      }
    );
  genuine = v.renderEntry e0;
  at = scopeCell: "[\"root\",\"inc\",\"settings\"] ← [${scopeCell},\"import\"] [include] d=1 merge";
in
{
  flake.tests.render-disclosure = {
    test-control-the-genuine-entry-renders-its-names = {
      expr = genuine;
      expected = at "\"inc\"";
    };
    test-a-set-renders-its-marker = {
      expr = withScope { inner = "inc"; };
      expected = at "‹set›";
    };
    test-a-lambda-renders-its-marker = {
      expr = withScope (x: x);
      expected = at "‹lambda›";
    };
    test-a-list-renders-its-marker = {
      expr = withScope [ "inc" ];
      expected = at "‹list›";
    };
    test-a-bool-renders-its-marker = {
      expr = withScope true;
      expected = at "‹bool›";
    };
    test-a-null-renders-its-marker = {
      expr = withScope null;
      expected = at "‹null›";
    };
    test-a-missing-field-renders-its-marker = {
      expr = v.renderEntry (builtins.removeAttrs e0 [ "distance" ]);
      expected = "[\"root\",\"inc\",\"settings\"] ← [\"inc\",\"import\"] [include] d=‹absent› merge";
    };
    test-a-number-and-a-path-render-as-values = {
      expr = {
        int = withScope 7;
        float = withScope 1.5;
        path = withScope /inc;
      };
      expected = {
        int = at "7";
        float = at "1.5";
        path = at "\"/inc\"";
      };
    };
    # The planted coercing values: each renders `‹set›`, never the `"inc"` it coerces to, which
    # would render it as the genuine entry.
    test-a-coercing-set-renders-its-marker-rather-than-its-string = {
      expr = {
        outPath = withScope { outPath = "inc"; };
        toString = withScope { __toString = _: "inc"; };
      };
      expected = {
        outPath = at "‹set›";
        toString = at "‹set›";
      };
    };
    # One malformed entry no longer hides the rest: every entry of the trace renders, the genuine
    # ones exactly as they did.
    test-a-malformed-entry-leaves-the-rest-of-the-trace-rendered = {
      expr = v.renderTrace [
        e0
        (e0 // { mode = x: x; })
        e0
      ];
      expected = [
        genuine
        "[\"root\",\"inc\",\"settings\"] ← [\"inc\",\"import\"] [include] d=1 ‹lambda›"
        genuine
      ];
    };
  };
}
