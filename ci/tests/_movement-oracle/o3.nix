# AC-7 / O3 — CONTENT BLINDNESS, AS A LIMIT AND NOT A DEFECT, with its live control.
#
# Two runs with IDENTICAL topology and DIFFERENT channel content must produce byte-equal traces.
# CONTROL: the same two runs must produce DIFFERENT channel values in the same run, else the arm
# proves nothing — byte-equal traces from two runs that were secretly the same run is a measurement
# of nothing at all.
#
# ★ THE TRACE IS gen-view's OWN `trace`/`hashTrace` — the instrument the content-blindness property
# is a property of at the destination (spec §9.5: O3 is substrate-internal).
{
  genView,
  fixture,
  corpus,
}:
let
  v = genView;
  f = fixture;

  placement = v.placement.place {
    mode = "nest";
    path = [ "settings" ];
    name = "settings";
    value = null;
  };
  hashOf = relation: v.hashTrace { inherit relation placement; };
  traceOf = relation: v.trace { inherit relation placement; };

  # ── THE PAIR ────────────────────────────────────────────────────────────────────────────────
  # Identical scopes, identical edges, identical carrier, identical declaration. EVERY datum value
  # replaced. Nothing structural moves: the relation each datum is filed under and the scope it sits
  # at are unchanged, so the reached set, the competition and the surviving set are the same.
  restate =
    tag:
    f.authored {
      root = [
        {
          relation = "import";
          datum = [ "${tag}-root" ];
        }
      ];
      mid = [
        {
          relation = "import";
          datum = [ "${tag}-mid" ];
        }
      ];
      inc = [
        {
          relation = "import";
          datum = [ "${tag}-inc" ];
        }
        {
          relation = "policy";
          datum = [ "${tag}-not-this-relation" ];
        }
      ];
    };

  graphOf =
    tag:
    v.scopeGraph {
      inherit (f) carrier scopes edges;
      data = restate tag;
    };

  runOne = f.mkRelation { graph = graphOf "ONE"; };
  runTwo = f.mkRelation { graph = graphOf "TWO"; };

  # ── A SECOND, HARDER PAIR — the datum is a THUNK that would throw if forced ──────────────────
  # `traceEntryOf` excludes every content thunk by construction, and the map refuses the datum by
  # name, so a trace must be takeable of a result whose content has NOT been forced. If any part of
  # the path from movement result to `hashTrace` touched the datum, this arm would throw.
  unforceableGraph = v.scopeGraph {
    inherit (f) carrier scopes edges;
    data = f.authored {
      root = [
        {
          relation = "import";
          datum = throw "AC-7/O3: the trace forced a datum";
        }
      ];
      mid = [
        {
          relation = "import";
          datum = throw "AC-7/O3: the trace forced a datum";
        }
      ];
      inc = [
        {
          relation = "import";
          datum = throw "AC-7/O3: the trace forced a datum";
        }
      ];
    };
  };
  unforceable = f.mkRelation { graph = unforceableGraph; };
  unforceableHash = builtins.tryEval (hashOf unforceable);

  # ★ THE UNFORCEABLE ARM'S OWN CONTROL: forcing the ANSWER of the same run must throw, or the
  # thunk was never a thunk and the arm proved nothing.
  unforceableAnswer = builtins.tryEval (builtins.deepSeq unforceable.value unforceable.value);
in
{
  hashOne = hashOf runOne;
  hashTwo = hashOf runTwo;
  byteEqual = hashOf runOne == hashOf runTwo;
  traceOne = traceOf runOne;

  # THE CONTROL — the two runs must differ in what they answered.
  control = {
    answerOne = runOne.value;
    answerTwo = runTwo.value;
    answersDiffer = runOne.value != runTwo.value;
    # and the topology must genuinely be identical, or "identical topology" was assumed not measured
    contributionsOne = builtins.map (c: {
      inherit (c)
        scope
        distance
        relation
        admission
        ;
      word = builtins.map (s: s.label) c.path;
    }) runOne.contributions;
    contributionsTwo = builtins.map (c: {
      inherit (c)
        scope
        distance
        relation
        admission
        ;
      word = builtins.map (s: s.label) c.path;
    }) runTwo.contributions;
  };

  unforced = {
    hashSucceeded = unforceableHash.success;
    hash = if unforceableHash.success then unforceableHash.value else null;
    # the control: the same run's ANSWER must throw
    answerSucceeded = unforceableAnswer.success;
  };

  # ── THE ARC'S OWN PAIR, RE-READ ─────────────────────────────────────────────────────────────
  # v1 arms A and E are the measurement record's designated discriminator-and-control pair. They
  # answer DIFFERENTLY (`["H-val"]` vs `["S-exposed"]`) over the SAME structural topology — one
  # contribution, at `H`, under `policy`, at distance 1, by the word `[ "parent" ]`. This is O3's
  # shape arriving from the corpus rather than from a fixture built to show it.
  armsAE =
    let
      c = corpus;
    in
    {
      hashA = hashOf c.arms.A.result;
      hashE = hashOf c.arms.E.result;
      byteEqual = hashOf c.arms.A.result == hashOf c.arms.E.result;
      answerA = c.arms.A.result.value;
      answerE = c.arms.E.result.value;
      answersDiffer = c.arms.A.result.value != c.arms.E.result.value;
    };
}
