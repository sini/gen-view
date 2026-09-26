# THE MOVEMENT ORACLE — THE §9.4 COLLISION PROBE, AT THE DESTINATION.
#
# The movement spec §9.4 records, measured at the frozen edge instrument: two structurally distinct
# entries — one with class `"c | y"` and path `[ "p" ]`, one with class `"c"` and path `[ "y | p" ]`
# — render BYTE-IDENTICAL sort keys, because the key was a separator-join over free strings; and the
# oracle is not thereby forged — the entries, the hashes and permutation invariance all separate.
#
# ★ THE KEY NO LONGER COLLIDES HERE, AND THAT IS THE LANDED BEHAVIOUR. gen-view's keys became the
# JSON of their component lists (`lib/placement.nix`, `ci/tests/key-encoding.nix`), so a component
# carrying the separator cannot shift a field boundary. AC-7 read `keysCollide = true` before that
# landed; the pair is kept as the witness that it now keys apart, beside the oracle's separation.
# The instrument half AC-7 also ran — the frozen edge library — retired (ADR-0010 §3, spec §9.5).
{ genView, fixture }:
let
  v = genView;

  # gen-view's key is `targetKey | pathKey | sourceKey | mode [| kind]`, each component the JSON of
  # its name tuple.
  mkContribution =
    { channel, datum }:
    {
      scope = "s";
      inherit channel;
      relation = "r";
      distance = 0;
      path = [ ];
      inherit datum;
    };
  mkPlacement =
    path:
    v.placement.place {
      mode = "nest";
      inherit path;
      name = "settings";
      value = null;
    };

  # THE COLLIDING PAIR, at gen-view's rendering.
  gvA = {
    contribution = mkContribution {
      channel = "c | y";
      datum = [ "A" ];
    };
    placement = mkPlacement [ "p" ];
  };
  gvB = {
    contribution = mkContribution {
      channel = "c";
      datum = [ "B" ];
    };
    placement = mkPlacement [ "y | p" ];
  };

  gvEntryA = v.traceEntryOf gvA;
  gvEntryB = v.traceEntryOf gvB;

  # THE LIVE CONTROL — two ORDINARY distinct entries must produce DISTINCT keys, or a "the keys
  # collide" reading is a reading of a broken instrument.
  gvCtlA = {
    contribution = mkContribution {
      channel = "c";
      datum = [ "A" ];
    };
    placement = mkPlacement [ "p" ];
  };
  gvCtlB = {
    contribution = mkContribution {
      channel = "d";
      datum = [ "B" ];
    };
    placement = mkPlacement [ "q" ];
  };

  # ★ `trace`/`hashTrace` TAKE ONE PLACEMENT FOR THE WHOLE RELATION, so the colliding pair — whose
  # two members differ in their PLACEMENT PATH — cannot be put in ONE gen-view trace. The separation
  # is therefore measured as gen-view can state it: two SINGLETON traces, whose hashes must differ.
  # That the pair is not co-traceable at this destination is itself the placement-arity finding and
  # is reported as such rather than worked around.
  #
  # `trace` takes a materialized view relation, so the probe's contributions ride on the fixture's
  # relation with its contribution list replaced; the trace reads nothing else of it.
  onRelation = cs: fixture.relation // { contributions = cs; };
  gvHash =
    x:
    v.hashTrace {
      relation = onRelation [ x.contribution ];
      inherit (x) placement;
    };

in
{
  destination = {
    keyA = v.edgeSortKey gvEntryA;
    keyB = v.edgeSortKey gvEntryB;
    keysCollide = v.edgeSortKey gvEntryA == v.edgeSortKey gvEntryB;
    entriesSeparate = builtins.toJSON gvEntryA != builtins.toJSON gvEntryB;
    hashA = gvHash gvA;
    hashB = gvHash gvB;
    hashesSeparate = gvHash gvA != gvHash gvB;
    control = {
      keyA = v.edgeSortKey (v.traceEntryOf gvCtlA);
      keyB = v.edgeSortKey (v.traceEntryOf gvCtlB);
      ordinaryKeysDiffer = v.edgeSortKey (v.traceEntryOf gvCtlA) != v.edgeSortKey (v.traceEntryOf gvCtlB);
    };
    # PERMUTATION INVARIANCE at the destination, on a co-traceable pair (one placement, two
    # contributions), measured rather than quoted.
    permutation =
      let
        c1 = mkContribution {
          channel = "c";
          datum = [ "1" ];
        };
        c2 = mkContribution {
          channel = "d";
          datum = [ "2" ];
        };
        p = mkPlacement [ "p" ];
        h =
          cs:
          v.hashTrace {
            relation = onRelation cs;
            placement = p;
          };
      in
      {
        forward = h [
          c1
          c2
        ];
        reversed = h [
          c2
          c1
        ];
        byteEqual =
          h [
            c1
            c2
          ] == h [
            c2
            c1
          ];
      };
  };

}
