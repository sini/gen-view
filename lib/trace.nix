# THE ORACLE CLUSTER — the structured trace, its sort key, the rendering, and the trace's
# structural fingerprint.
#
# ★★ WHY THIS CLUSTER IS BUILT HERE BEFORE ANYTHING RETIRES. These six constructs are THE
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
  elements = import ./elements.nix { inherit prelude; };
  inherit (refusal)
    fields
    refuse
    renderValue
    decided
    choice
    strings
    ;
  inherit (placement) pathKey targetKey sourceKey;

  # `edgeSortKey` — the `T | P | S | M [| K]` key. The skeleton is fixed; the components' text is
  # not: T, P and S are the JSON name tuples of `targetKey`/`pathKey`/`sourceKey`, so each ends at
  # a point no name can move. The kind component is APPENDED only when present, so an entry that
  # carries no kind renders the four-component form rather than gaining an empty field.
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
      target = placement.targets.root {
        scope = c.scope;
        channel = c.channel;
      };
      mode = choice "traceEntryOf" "placement.mode" placement.modes (p.mode or null);
      path = strings "traceEntryOf" "placement.path" (p.path or null);
      contributionFields = [
        "scope"
        "channel"
        "relation"
        "distance"
        "path"
      ];
    in
    if !(builtins.isAttrs c) || !(builtins.all (f: builtins.hasAttr f c) contributionFields) then
      refuse "traceEntryOf" "field 'contribution' is ${renderValue c}; it must be a view relation's contribution, carrying ${builtins.concatStringsSep ", " contributionFields}"
    else if !(builtins.isString c.relation) || c.relation == "" then
      refuse "traceEntryOf" "the contribution's relation is ${renderValue c.relation}; it must be a non-empty relation name"
    else if !(builtins.isInt c.distance) then
      refuse "traceEntryOf" "the contribution's distance is ${renderValue c.distance}; it must be an int"
    else if
      !(builtins.isList c.path)
      || !(builtins.all (s: builtins.isAttrs s && builtins.isString (s.label or null)) c.path)
    then
      refuse "traceEntryOf" "the contribution's path must be a list of steps, each carrying a string label"
    else if !(builtins.isAttrs p) then
      refuse "traceEntryOf" "field 'placement' is ${renderValue p}; it must be a placement carrying `mode` and `path`"
    else
      decided [ target mode path ] {
        inherit target;
        source = {
          inherit (c) scope relation;
        };
        inherit mode path;
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
  # Primary key: the sort key. Secondary: the canonical JSON of the entry itself, so the
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
      ) (elements.contributionsOf "trace" a.relation);
      checked =
        if !(builtins.isAttrs a.relation) then
          refuse "trace" "field 'relation' is ${renderValue a.relation}; it must be a materialized view relation"
        # The tag test is `elementOf`'s, which re-checks what the tag claims.
        else if !(builtins.isAttrs (elements.elementOf "trace" "relation" "viewRelation" a.relation)) then
          false
        else if !(builtins.isAttrs a.placement) then
          refuse "trace" "field 'placement' is ${renderValue a.placement}; it must be a placement carrying `mode` and `path`"
        else
          builtins.seq (choice "trace" "placement.mode" placement.modes (a.placement.mode or null)) (
            builtins.isList (strings "trace" "placement.path" (a.placement.path or null))
          );
      ord =
        x: y:
        let
          kx = edgeSortKey x;
          ky = edgeSortKey y;
        in
        if kx != ky then kx < ky else builtins.toJSON x < builtins.toJSON y;
    in
    decided [ checked ] (sort ord entries);

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

  # `hashTrace { relation; placement; }` — the topology's structural fingerprint: `sha256` over the
  # canonical JSON of the trace. Content-independent, because the trace it hashes is: an entry
  # carries identities and never a datum, so two runs differing only in what their channels resolved
  # to fingerprint alike, and that is a limit of the instrument rather than a defect in it.
  #
  # ★★ THE PREIMAGE ARGUMENT IS WHY THE HASH IS TAKEN OVER THE TRACE AND NEVER OVER THE SORT KEY.
  # The key above is a PROJECTION of the entry: it carries neither the witness distance nor the
  # word, so two structurally distinct entries — one contribution reached at distance 1 and at
  # distance 3 — render one key. The key is therefore not preimage-injective, and a fingerprint
  # built on it would mint one value for that pair. (Its components no longer shift into one
  # another: each is the JSON of its name tuple.) The trace encoding has no such route: canonical
  # JSON carries every component under its own name, so entries that collide on the key still
  # separate here. The key's collision degrades `trace`'s PRIMARY order to a tie and the
  # canonical-JSON secondary resolves it — which is what the secondary is for.
  #
  # ★ PERMUTATION INVARIANCE IS INHERITED, NOT RESTATED. `trace` is a function of the entry SET, so
  # two presentations of one set reach `toJSON` byte-equal and there is nothing left here to make
  # order-independent.
  hashTrace = args: builtins.hashString "sha256" (builtins.toJSON (trace args));
in
{
  inherit
    edgeSortKey
    traceEntryOf
    trace
    renderEntry
    renderTrace
    hashTrace
    ;
}
