# THE ORACLE CLUSTER — the structured trace, its frozen sort key, and the rendering.
#
# ★★ WHY THIS CLUSTER IS BUILT HERE BEFORE ANYTHING RETIRES. These five constructs are THE
# INSTRUMENT THAT VALIDATES THE SPEC THAT RETIRES THEM. A plan that retired them alongside the
# rest would remove its own oracle, so they must be EXPRESSIBLE HERE FIRST — and the ordering is
# not a courtesy: the key below is built on the PATH and the MODE, which are placement components,
# so the cluster is downstream of placement having a home and upstream of the retirement.
#
# ★★ AND THE CLAIM THIS MAKES IS A VOCABULARY CLAIM, NOT A SEMANTIC-EQUIVALENCE ONE. Nothing here
# asserts byte-identity with the frozen rendering of the surface it re-expresses; that round trip
# is a disclosed gap and is not discharged by anything in this file. What is claimed is that the
# CAPABILITY — an identity-only trace, totally ordered, renderable — is expressible over this
# library's own published surface.
#
# ★ IDENTITY ONLY, NEVER RESOLVED CONTENT. `traceEntryOf` carries the scope, the channel, the
# relation, the distance and the path's LABEL WORD, and it never carries the datum. That is what
# lets a trace be taken of a result whose content has not been forced — the property the frozen
# instrument has and the one a naive projection of the whole contribution would lose on its first
# use.
{ prelude }:
let
  inherit (prelude)
    map
    sort
    concatStringsSep
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  placement = import ./placement.nix { inherit prelude; };
  inherit (refusal) fields;
  inherit (placement) pathKey targetKey sourceKey;

  # `edgeSortKey` — the frozen `T | P | S | M [| K]` key. The kind component is APPENDED only when
  # present, so an entry that carries no kind renders the historical four-component form
  # unchanged rather than gaining an empty field.
  edgeSortKey =
    entry:
    targetKey entry.target
    + " | "
    + pathKey entry.path
    + " | "
    + sourceKey entry.source
    + " | "
    + entry.mode
    + (if (entry.kind or null) == null then "" else " | " + entry.kind);

  # `traceEntryOf { contribution; placement; }` — the structured identity entry.
  traceEntryOf =
    args:
    let
      a = fields "traceEntryOf" [
        "contribution"
        "placement"
      ] args;
      c = a.contribution;
      p = a.placement;
    in
    {
      target = placement.targets.root {
        scope = c.scope;
        channel = c.channel;
      };
      source = {
        inherit (c) scope relation;
      };
      inherit (p) mode path;
      # The KIND component: the relation the datum was reached under. Under the scoped-relations
      # arrangement this is exactly what a typed edge's label used to carry, moved to the sort it
      # belongs in.
      kind = c.relation;
      inherit (c) distance;
      # The path's LABEL WORD — the witness, reduced to its structural content. Never the datum.
      word = map (step: step.label) c.path;
    };

  # `trace { relation; placement; }` — a TOTAL order over the entries.
  #
  # Primary key: the frozen sort key. Secondary: the canonical JSON of the entry itself, so the
  # trace is a pure function of the SET even where two contributions share a sort key but differ in
  # identity; only genuinely identical entries collapse to an order-irrelevant tie.
  trace =
    args:
    let
      a = fields "trace" [
        "relation"
        "placement"
      ] args;
      entries = map (
        c:
        traceEntryOf {
          contribution = c;
          inherit (a) placement;
        }
      ) a.relation.contributions;
      ord =
        x: y:
        let
          kx = edgeSortKey x;
          ky = edgeSortKey y;
        in
        if kx != ky then kx < ky else builtins.toJSON x < builtins.toJSON y;
    in
    sort ord entries;

  # DISPLAY RENDERING — strings are derived HERE and nothing consumes them programmatically.
  renderEntry =
    entry:
    targetKey entry.target
    + " ← "
    + sourceKey entry.source
    + " ["
    + concatStringsSep "." entry.word
    + "] d="
    + toString entry.distance
    + " "
    + entry.mode;

  renderTrace = entries: map renderEntry entries;
in
{
  inherit
    edgeSortKey
    traceEntryOf
    trace
    renderEntry
    renderTrace
    ;
}
