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
    renderSubject
    attrKey
    ;
  inherit (placement) pathKey targetKey sourceKey;

  # `edgeSortKey` — the `T | P | S | M [| K]` key. The skeleton is fixed; the components' text is
  # not: T, P and S are the JSON name tuples of `targetKey`/`pathKey`/`sourceKey`, so each ends at
  # a point no name can move. The kind component is APPENDED only when present, so an entry that
  # carries no kind renders the four-component form rather than gaining an empty field.
  sortKeyOf =
    entry:
    targetKey entry.target
    + " | "
    + pathKey entry.path
    + " | "
    + sourceKey entry.source
    + " | "
    + entry.mode
    + (if (entry.kind or null) == null then "" else " | " + entry.kind);

  # `sortEntry entry` — THE CHECK ON THE FIELDS `edgeSortKey` READS, returning the entry unchanged
  # (`rootNames`' rule). `edgeSortKey` is published over any entry, and a hand-built one reaches it
  # without passing `traceEntryOf`, so it is owed the refusals `traceEntryOf` would have given it:
  # `+` aborts past `tryEval` on a value it cannot coerce, and silently coerces an
  # `outPath`/`__toString` set to its string. A sort key must be INJECTIVE on what it orders, and a
  # key built from a coerced value is not, so the entry is REFUSED BY NAME rather than keyed
  # (`den-hoag-g1qy0`). `kind` is optional; the target, the path and the source are checked by the
  # keys that read them (`targetKey`, `pathKey`, `sourceKey`).
  sortEntry =
    e:
    let
      missing = builtins.filter (n: !(builtins.hasAttr n e)) [
        "target"
        "source"
        "mode"
        "path"
      ];
    in
    if !(builtins.isAttrs e) then
      refuse "edgeSortKey" "field 'entry' is ${renderValue e}; it must be a trace entry, as `traceEntryOf` mints"
    else if missing != [ ] then
      refuse "edgeSortKey" "the entry carries no '${builtins.head missing}'; it must be a trace entry, as `traceEntryOf` mints"
    else if !((e.kind or null) == null || builtins.isString e.kind) then
      refuse "edgeSortKey" "the entry's kind is ${renderValue e.kind}; it must be a relation name"
    else
      builtins.seq (choice "edgeSortKey" "mode" placement.modes e.mode) e;

  edgeSortKey = entry: sortKeyOf (sortEntry entry);

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
          kx = sortKeyOf x;
          ky = sortKeyOf y;
        in
        if kx != ky then kx < ky else builtins.toJSON x < builtins.toJSON y;
    in
    decided [ checked ] (sort ord entries);

  # DISPLAY RENDERING — strings are derived HERE and nothing consumes them programmatically.
  #
  # ★ DISCLOSED BY TYPE, NEVER COERCED (`den-hoag-g1qy0`). `renderEntry` is published over any
  # entry, and a hand-built one may carry anything in any field. Each leaf is dispatched on
  # `builtins.typeOf`: a string, a number and a path render as values, and every other type renders
  # as its marker (`‹set›`, `‹lambda›`, `‹list›`, `‹bool›`, `‹null›`), as does a record or list
  # position holding something else, and `‹absent›` a missing field. Nothing is coerced, so an
  # `outPath`/`__toString` set renders `‹set›` rather than the string it would coerce to, and no
  # field aborts the rendering: one malformed entry cannot hide the rest of a `renderTrace`. The
  # price is the one a display is allowed: two distinct values may render alike (two sets, a path
  # and its string). Inside a key tuple a marker stands unquoted, where no name can.
  renderEntry =
    let
      marker = x: "‹${builtins.typeOf x}›";
      absent = "‹absent›";
      shown =
        x:
        let
          t = builtins.typeOf x;
        in
        if t == "string" then
          x
        else if t == "int" || t == "float" then
          builtins.toJSON x
        else if t == "path" then
          toString x
        else
          marker x;
      cell = x: if builtins.isString x || builtins.isPath x then builtins.toJSON (shown x) else shown x;
      tuple = xs: "[" + concatStringsSep "," xs + "]";
      field = r: n: if builtins.hasAttr n r then r.${n} else null;
      leaf = r: n: if builtins.hasAttr n r then shown r.${n} else absent;
      leafCell = r: n: if builtins.hasAttr n r then cell r.${n} else absent;
      record = r: body: if builtins.isAttrs r then body r else marker r;
      target =
        t:
        if (field t "arm") == "output" then
          tuple [
            (cell "out")
            (
              if !(builtins.hasAttr "path" t) then
                absent
              else if builtins.isList t.path then
                tuple (map cell t.path)
              else
                marker t.path
            )
          ]
        else
          tuple [
            (cell "root")
            (leafCell t "scope")
            (leafCell t "channel")
          ];
      source =
        src:
        tuple [
          (leafCell src "scope")
          (leafCell src "relation")
        ];
      word =
        e:
        if !(builtins.hasAttr "word" e) then
          absent
        else if builtins.isList e.word then
          concatStringsSep "." (map shown e.word)
        else
          marker e.word;
      part =
        e: n: render:
        if builtins.hasAttr n e then record e.${n} render else absent;
    in
    entry:
    record entry (
      e:
      part e "target" target
      + " ← "
      + part e "source" source
      + " ["
      + word e
      + "] d="
      + leaf e "distance"
      + " "
      + leaf e "mode"
    );

  # A trace is a list; anything else has no rows to disclose, so it is refused by name.
  renderTrace =
    entries:
    if builtins.isList entries then
      map renderEntry entries
    else
      refuse "renderTrace" "field 'entries' is ${renderValue entries}; it must be a list of trace entries, as `trace` returns";

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

  # `joinedTrace { relation; placement; positions; innerOf; }` — the trace of a relation materialized
  # over `headPositions`, each entry joined to the record its contributor's OWN evaluation keeps.
  #
  # ★★ THE JOIN READS NOTHING BUT THIS LIBRARY'S TRACE AND THE CALLER'S RECORDS. The head letter is
  # already in the entry's word (its first letter), and the contributor is the position's owner, so
  # the substrate side needs no new fact. What happened INSIDE the contributor is the caller's to
  # supply: `innerOf scope` returns that scope's record for the channel, opaque here except for the
  # fields the door reads — `scope` and `loc`, and `band` if the value moved or `reason` if it did
  # not — or `null` for a scope that contributes nothing. A caller-supplied function is this
  # library's standing shape (`keyOf`, `combine`, `wellFormed`), and its output is data.
  #
  # ★★ EVERY STRUCTURAL SCOPE IS ASKED, NOT ONLY THE TRACE'S. A scope whose field was not moved puts
  # nothing in the relation, so the substrate's own record never mentions it; `unset` is where it is
  # recorded, which is what keeps a value that did not move from vanishing silently.
  #
  # ★ `innerOf`, PER FAILURE MODE (door or falsifier, never a silent reading):
  #   · a missing or non-record result for a contributor in the trace → refused by name, naming it
  #   · a record whose `scope` is another contributor's (a mis-keyed join) → refused by name: the
  #     record's `scope` is compared with the position's owner
  #   · a record carrying both `band` and `reason` → refused by name: it would be reported as moved
  #     and as not moved at once
  #   · a throw → propagates, as the caller's own error
  #
  # ★★ AND A MOVED VALUE THE RELATION NEVER ACCOUNTS FOR IS RECORDED, NOT REFUSED. A `band` record
  # whose scope owns no position among the relation's `contributions`, `shadowed`, `withheld` or
  # `dropped` goes to `unaccounted`, record intact. It covers a datum never placed, a relation
  # materialized from another root, and a datum the definition's `wellFormed` rejected — which is
  # lawful and which the relation records nowhere, so a refusal here would reject lawful input.
  joinedTrace =
    args:
    let
      site = "joinedTrace";
      a = fields site [
        "relation"
        "placement"
        "positions"
        "innerOf"
      ] args;
      p = a.positions;
      positionsOk =
        if
          !(builtins.isAttrs p && builtins.isAttrs (p.owners or null) && builtins.isList (p.scopes or null))
        then
          refuse site "field 'positions' is ${renderValue p}; it must be what `headPositions` returns, carrying `owners` and `scopes`"
        else if !(builtins.isFunction a.innerOf) then
          refuse site "field 'innerOf' is ${renderValue a.innerOf}; it must be a function from a contributor's scope to its record, or null"
        else
          true;
      recordOf =
        s:
        let
          r = a.innerOf s;
        in
        if r == null then
          null
        else if
          !(
            builtins.isAttrs r
            && builtins.isString (r.scope or null)
            && builtins.isList (r.loc or null)
            && (r ? band || r ? reason)
          )
        then
          refuse site "innerOf returned ${renderValue r} for the contributor ${renderSubject s}; a record carries `scope`, `loc`, and `band` (it moved) or `reason` (it did not), and a scope that contributes nothing returns null"
        else if r ? band && r ? reason then
          refuse site "innerOf returned a record for the contributor ${renderSubject s} carrying both `band` and `reason`; a record says the value moved (`band`) or that it did not (`reason`), never both"
        else if r.scope != s then
          refuse site "innerOf returned the record of ${renderSubject r.scope} for the contributor ${renderSubject s}; a record is joined only to its own contributor's position, and this one is mis-keyed"
        else
          r;
      records = builtins.listToAttrs (
        map (s: {
          name = attrKey s;
          value = recordOf s;
        }) p.scopes
      );
      # every scope owning a position the relation reports, under any of its dispositions
      accounted = builtins.listToAttrs (
        map
          (x: {
            name = attrKey (p.owners.${attrKey x.scope} or { scope = ""; }).scope;
            value = null;
          })
          (
            a.relation.contributions
            ++ a.relation.shadowed
            ++ a.relation.withheld
            ++ map (d: d.contribution) a.relation.dropped
          )
      );
      joinEntry =
        e:
        let
          o = p.owners.${attrKey e.source.scope} or null;
          r = records.${attrKey o.scope};
        in
        if o == null then
          refuse site "the trace entry from ${renderSubject e.source.scope} is not at a position of field 'positions'; the relation was materialized over a different graph"
        else if r == null || !(r ? band) then
          refuse site "innerOf returned ${renderValue r} for the contributor ${renderSubject o.scope}, whose datum survives in the trace; it must be the record of a value that moved, carrying `band`"
        else
          {
            entry = e;
            contributor = o.scope;
            band = builtins.head e.word;
            inner = r;
          };
    in
    decided [ positionsOk ] {
      joined = map joinEntry (trace {
        inherit (a) relation placement;
      });
      unset = builtins.filter (r: r != null && r ? reason) (map (s: records.${attrKey s}) p.scopes);
      unaccounted = builtins.filter (r: r != null && r ? band && !(accounted ? ${attrKey r.scope})) (
        map (s: records.${attrKey s}) p.scopes
      );
    };
in
{
  inherit
    edgeSortKey
    traceEntryOf
    trace
    renderEntry
    renderTrace
    hashTrace
    joinedTrace
    ;
}
