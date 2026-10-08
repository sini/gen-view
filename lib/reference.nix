# REFERENCE RESOLUTION — a defining query whose COMPUTE IS TOTAL DELEGATION to an injected query
# authority.
#
# ★ TWO CONSTRUCTS LIVE HERE, one per direction of one relation: `referenceResolution` reads the
# imports of an id, `neededBy` gathers the nodes that import it. Their second half is at the foot
# of this header; the two helpers they share sit at module scope, lifted there so that ONE fact
# about the delegate has ONE statement.
#
# ── THE TERM, AND IT IS THE PRIMARY'S OWN ────────────────────────────────────────────────────
# Néron, Tolmach, Visser & Wachsmuth, "A Theory of Name Resolution", ESOP 2015. "Reference
# resolution" is the NAME OF A RULE in the resolution calculus — Fig. 3 rule (X), and again as rule
# (X′) of Fig. 19, the primed calculus carrying the 'seen scopes' component. That rule is exactly
# what this construct declares:
#
#     the reference x^R_i in scope S resolves to the declaration x^D_j reachable from S, with the
#     D < I < P specificity of Fig. 2 deciding among candidates.
#
# Corroborated at van Antwerpen, Poulsen, Rouvoet & Visser 2018, "Scopes as Types".
#
# ★★ `referenceAttribute` IS *NOT* THE NAME, THOUGH THE TERM IS WELL ATTESTED. Hedin 2000 is
# explicit: "The value of a reference attribute is the (unique) identity of the denoted node." This
# construct's value is the CALLER'S PROJECTION of the resolved node's datum and never a node
# identity, so taking that term would carry a claim TRUE AT THE SOURCE AND FALSE HERE. Hedin 2000
# is cited for the attribute-grammar FRAMING — an attribute at one node whose value is reached
# through another — and is not this construct's name.
#
# ── THE DEFINING QUERY ───────────────────────────────────────────────────────────────────────
# The `project`ion of the datum at the node the delegate's resolution reaches from an id, among the
# nodes whose datum satisfies `wellFormed` — π_project ∘ σ_wellFormed over the visible-declaration
# set of that id, with D < I < P ordering local vs imported vs inherited as the two declared
# shadowing flags decide, and the import relation traversed one hop or transitively as
# `transitiveImports` declares. The query's domain is the node itself (the LOCAL candidate), the
# nodes reached along the delegate's import relation (the IMPORTED candidates), and the node's
# parent chain (the INHERITED candidate).
#
# ★★ TWO FIELDS AND NOT ONE, BECAUSE THE QUERY HAS TWO OPERATORS. A single predicate that both
# admits and projects cannot be split into π and σ, so no defining query could be stated for it at
# all — and such a predicate uses `null` for both "not a binding here" and "the value", so a datum
# whose projection is legitimately null is indistinguishable from an absent binding and vanishes
# with nothing saying so. The split is not free: the fused form binds its datum once and reuses it,
# where two fields are two thunks that each reach it, so the lookup runs twice per admitted node
# per query. No extra traversal and no extra force of the delegate's walk. It is taken because the
# defining-query form is unwritable without it, and a caller who wants the single bind can still
# write both fields over a shared `let` in its own scope.
#
# ── THE ANTI-DRIFT CONDITION, WHICH IS THE WHOLE DESIGN ──────────────────────────────────────
# ★★★ THIS FILE CONTAINS NO SHADOWING, NO TRAVERSAL AND NO CANDIDATE ORDERING. Every one of those
# words belongs to the delegate. The compute is `engine.resolve { … }` — the one resolution calculus
# (den-hoag-gayc) — and nothing else, so a change at the delegate arrives here as a change in
# BEHAVIOUR rather than as a divergence between two implementations of one mechanism. A later
# author who "optimizes" a shadowing decision into this file has built a second resolution
# implementation, and the delegation oracle is what fails then.
#
# ★★ THE MARKS ARE THE DELEGATE'S TOO. ADR-0026's boundary mark, the fail-closed floor "compiled
# into every query's effective reachability policy", is read by `resolve` itself at the source of
# every edge it considers. This construct's `marks` field is handed over as `bound`, the query's
# narrowing: it only removes edges, beside the floor the evaluation declares, so widening is
# unsayable. Nothing here classifies an edge.
#
# ★★ THE REFUSAL OF A MULTI-CANDIDATE IMPORT SET IS THE DELEGATE'S TOO — POINTED AT, NEVER
# RESTATED HERE. D < I < P orders the three SORTS; nothing in Fig. 2 orders candidates AMONG the
# imports, and nothing here or there supplies an order in its place. gen-scope's `single` REFUSES
# such a set BY NAME: an import set contributed by more than one DISTINCT declaring node is an
# ambiguity in Néron's sense (§2.2, Duplicate Declarations), and the query throws rather than
# choosing among the candidates or folding them together. A node reached along several routes — a
# repeated edge, a diamond — is ONE declaration reached several ways, and is not refused. ⇒ A
# SUCCESSFUL RESOLUTION COMES FROM EXACTLY ONE CONTRIBUTING DECLARATION, BY REFUSAL AND NOT BY
# ORDERING, so the value IS the datum of one node and Néron rule (X)'s one declaration is exactly
# what comes back; `null` remains the delegate's "no visible binding" answer and never an empty
# gather.
#
# ★★★ WHICH IS WHY THERE IS NO `codomain` FIELD, AND THE REASON IS WORTH MORE THAN THE FIELD WAS. A
# literal such as `codomain = "atMostOne"` written HERE would be a constant about a fact owned
# THERE — and A REFUSAL IS NOT A CARDINALITY: the delegate answers with one declaration or throws,
# and a literal naming a bound would misdescribe the second arm as a count. The refusal fires
# inside the delegate's closure, over the candidate set its walk assembles from the nodes
# `wellFormed` admits — a set that does not exist until the query runs: no constructor can inspect
# a closure's branch, and no construction-time check can know that set. The fact is therefore not
# derivable here, and a field carrying it would duplicate a fact the delegate owns — so it is not
# published; it is POINTED AT, above. Nothing that could go stale is written down.
#
# ── WHAT IS DELIBERATELY NOT A FIELD ─────────────────────────────────────────────────────────
# THE RELATION. A view's defining query should name its relation and `viewDefinition` requires one.
# This construct declares none, because the only honest source for the name is the delegate's own
# traversal vocabulary, which is a PRIVATE module there. A declared `relation` field would be an
# UNCHECKED declaration — the caller re-spelling a literal — and that module's own argument is the
# argument against it: agreement between two written-down literals is a coincidence rather than a
# property, and when they drift the answer is computed over a stale relation with nothing in the
# result distinguishing it from a correct one. The relation is the delegate's, named at the
# delegate, and this construct points at it.
#
# NO WALK PARAMETERS AND NO CARRIER ELEMENTS. A channel, a relation, an admission expression, a
# label order, a distance rule, a competition key and its disposal are the parameters of a WALK
# OVER A SCOPE GRAPH. This construct performs no walk of its own and holds no competition to
# dispose, so requiring them would be ceremony that decides nothing — the opposite failure to a
# silent default, and just as dishonest. A `root` is declined for a sharper reason still: the walk
# starts at the id the evaluator hands `compute` AT FORCE TIME, so a declared root would be a
# second, disagreeing origin.
#
# `wellFormed` IS CARRIED, deliberately and under its own name — van Antwerpen 2018 Fig. 1's WFD,
# data-term well-formedness. ★ NARROWED, and the citation is made in this form or not at all: WFD
# is a predicate over DATA TERMS, while the delegate hands the predicate the NODE RECORD whose
# declarations carry the datum, so what rides here is WFD composed with the node's datum
# projection.
#
# The retiring wrapper's `kind`, `readsAttrs` and `stratum` do not come across: they are that
# library's Equation grammar, read by its own scheduling apparatus, and the sole consumer takes
# `.compute` off the record and installs the bare function rather than feeding the record to a
# schedule. Re-publishing them would re-erect a retiring library's grammar inside its successor.
# `compute` KEEPS ITS NAME precisely because that is the property the consumer depends on.
#
# ── THE AUTHORITY IS INJECTED, AND THAT IS WHAT KEEPS THIS LIBRARY EVALUATOR-FREE ────────────
# The membership authority is injected INTO THE CONSTRUCTOR, so this library acquires no evaluator,
# no scope-graph engine, and no dependency edge onto one — the caller supplies the authority. A
# value publishing no `resolve` is refused BY NAME at construction rather than at some later force.
# ★ AND THE QUERY IS NARROWED. `marks` is REQUIRED and undefaulted — "no marks" is `_: [ ]` written
# down, because a boundary the query may omit fails open (ADR-0026's rejected candidate (b)) — and
# it reaches the authority as `bound`. `wellFormed` and `project` read the authority's own node
# record: a mark removes an edge, and never changes a value at a node the query legitimately
# reached.
# ★ Considered and not taken: making the authority a curried first argument
# (`referenceResolution engine { … }`). One attrset keeps this construct uniform with every other
# constructor here and lets the shipped two-sided field check cover the authority too.
#
# ══ `neededBy` — THE REVERSE HALF, A SECOND CONSTRUCT AND NOT A `direction` FIELD ═════════════
#
# ── THE DEFINING QUERY ───────────────────────────────────────────────────────────────────────
# The `project`ion of the datum at each node that IMPORTS an id, among those nodes whose datum
# satisfies `wellFormed` — π_project ∘ σ_wellFormed over the INVERSE of the delegate's `imports`
# relation, traversed one hop or to the reverse-import closure as `transitive` declares.
#
# ★★ UNDER MARKS IT IS THE INVERSE OF THE *BOUNDED* RELATION, and the bound is the forward one: an
# importer's edge is withheld by the IMPORTER's marks, the node the edge leaves, so `t` is needed
# by `o` exactly when `o` reads `t`. A boundary is an absent edge, absent in both directions;
# classifying the reverse step at `t` instead would give one relation two boundary semantics, and
# `neededBy` would stop being the stated inverse of what `referenceResolution` reads. The delegate
# holds this by construction: `resolve { direction = "inbound"; }` applies the marks to the
# AUTHORED graph before the converse is taken (ADR-0024).
#
# ★★ THE INVERSE IS THE DELEGATE'S CONVERSE, NEVER A TRANSPOSE HELD HERE. The delegate enumerates an
# id's importers over its node set, and this construct holds no transpose at all.
#
# THE QUERY'S DOMAIN is the importers of the id, and THE ID ITSELF IS NOT IN ITS OWN DOMAIN — a
# node carrying its own datum AND importing another still answers only its importers'. There is no
# LOCAL candidate in a reverse gather, which is the sharpest structural difference from the
# forward arm above.
#
# CARDINALITY, ORDER AND DEDUP ARE THE DELEGATE'S, POINTED AT AND NEVER RESTATED. It neither sorts
# nor deduplicates: a node reachable along two reverse paths CONTRIBUTES TWICE, because a reverse
# gather counts contributions. A caller needing a set or a stable total order does that at its own
# call site, and this construct's `transitive = true` arm asserts the duplicate rather than hiding
# it.
#
# ── WHY THIS IS A SECOND CONSTRUCT ───────────────────────────────────────────────────────────
# ★★★ NOT ONE CONSTRUCT WITH A `direction` FIELD, AND THE DISCIPLINES ARE WHY. The forward arm
# answers ONE datum or REFUSES — the delegate throws on more than one distinct contributor, an
# ambiguity in Néron's sense — while this arm GATHERS a multi-contributor set with no refusal at
# all. One `direction` field would select opposite DISPOSITIONS of a different SHAPE, which is a
# semantics chosen by a field value and unstatable as one defining query. Where direction is only
# direction one field is right, and `viewRelation`'s own `direction` is the confirming case: there
# both arms share shape and share discipline, and the field touches exactly one step of one
# pipeline.
#
# ★ NOR A SECOND ACCESS PATH TO `viewRelation { direction = "inbound"; }`, which walks a HELD
# GRAPH from a DECLARED root and holds a walk, a competition, a tie-set and a dedup. This
# construct reaches the evaluator's live node set through an injected authority from the id handed
# `compute` AT FORCE TIME, and holds none of those. The precedent is landed and is read at its
# stated scope: the forward walk did not make `referenceResolution` redundant, on a ground that
# never mentions direction at all.
#
# ── THE TERM, AND THE DISCLOSURE THAT TRAVELS WITH IT ────────────────────────────────────────
# `neededBy` is the owner's name, ruled as the stated inverse of `includes`. ★★ IT IS NOT A BASE
# RELATION: it is a RULE-DEFINED RELATION MADE TO APPEAR AS ONE — Manchanda & Warren, Minker (ed.)
# 1988 ch. 10, PRINTED 381 — whose defining rule is the paragraph above. That is what makes it a
# VIEW rather than an inverted lookup, an inverted lookup being a materialized index with no name
# and no rule.
#
# ★★ THE CLAIMED-FROM-NO-PAPER DISCLOSURE IS INHERITED AND IS NEVER DROPPED. The delegate's
# converse order (importers in `allNodeIds` order) is that library's OWN rule, claimed from no
# paper, and the citation its retired reverse operator used to carry was measured FALSE at the
# primary. This construct inherits the disclosure and not the citation.
#
# ── WHAT IS DELIBERATELY NOT A FIELD HERE ────────────────────────────────────────────────────
# THE SHADOWING FLAGS. There is no shadowing in a gather — D < I < P orders SORTS of candidate and
# a reverse gather has exactly one sort — and `transitive` is the only discipline it has.
#
# A `dedup` OR AN ORDER. `viewDefinition` requires both because it holds a competition; this
# construct holds none, and a fold written here would be this library implementing one the
# delegate owns.
#
# A `codomain`, A `relation` AND A `root`, each declined for the forward half's own reason, one
# relation over.
{ prelude, graph }:
let
  inherit (prelude)
    filter
    head
    concatMap
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    renderValue
    returned
    marksContract
    ;

  # σ's verdict, checked where it is read: the delegate reads it as a branch.
  admitted =
    site: resultName: node: v:
    returned site "result '${resultName}': 'wellFormed' (σ) at node ${nodeLabel node}"
      "it is a predicate on the authority's node record and must return a bool"
      builtins.isBool
      v;

  # ── THE TWO HELPERS BOTH CONSTRUCTS SHARE, AT MODULE SCOPE ───────────────────────────────────
  # ★★ ONE GUARD FOR ONE DELEGATE CONVENTION, WHICH IS WHY IT IS LIFTED RATHER THAN COPIED. The
  # null-projection guard states ONE fact about ONE authority — that its `dataFilter` reads `null`
  # as NO BINDING HERE — and both directions of `resolve` hold it: an inbound gather DROPS a null
  # contribution exactly as the forward selection reads one as an absent binding. Two copies in two
  # `let`s would be two statements of one fact, which is the drift class this file declines a
  # `relation` field over.

  # The node label used in the materialization refusal below. The engine is injected and is
  # required only to publish its own operator, so the id is read where the record carries one
  # rather than assumed — a refusal that threw while building its own message would replace a named
  # failure with an anonymous one.
  nodeLabel =
    node:
    if node ? id && builtins.isString node.id then
      "'${node.id}'"
    else
      "(the engine's node record carries no 'id')";

  # ★ THE REFUSAL THAT CLOSES THE FUSED PREDICATE'S THIRD DEFECT, and the only refusal in this file
  # that fires at MATERIALIZATION rather than at construction. The delegate reads `null` as "no
  # binding here", so a well-formed node whose projection is null would be read as an ABSENCE and
  # the value would vanish with nothing saying so. An empty answer is never a refusal in this
  # library — and here the converse is what bites: a refusal must never arrive wearing the shape of
  # an empty answer.
  #
  # ★★ IT TAKES `site` AND `resultName`, AND THE MESSAGE BODY TAKES NO THIRD PARAMETER — which is a
  # claim about the delegate rather than a convenience. The sentence about null is true of BOTH
  # directions, so one message states one fact. What differs between the two call sites is only
  # WHICH construct refused and under WHAT result name: the two coordinates a caller who meets this
  # while forcing an attribute far from the declaration cannot act without.
  requireNonNull =
    site: resultName: node: value:
    if value == null then
      refuse site "result '${resultName}': node ${nodeLabel node} is admitted by 'wellFormed' and its 'project' returned null; the query authority reads null as NO BINDING HERE, so a null projection would be indistinguishable from an absent one"
    else
      value;

  # π ∘ σ, the relation's lookup composed with WFD: `resolve`'s `dataFilter`, applied by the
  # authority to its own node record. A mark removes an edge and never rewrites a record, so σ and π
  # read exactly the node the walk reached.
  filterOver =
    site: a: n:
    if admitted site a.name n (a.wellFormed n) then
      requireNonNull site a.name n (a.project n)
    else
      null;

  # The `marks` field, checked at construction and handed on as the checked per-node accessor —
  # the one statement of the contract `viewRelation` also reads, at this construct's site. It is
  # passed to the authority as `bound`, the query's narrowing (gen-scope D3): it only removes edges,
  # beside the floor the evaluation itself declares, so widening is unsayable.
  marksAt =
    site: marks:
    let
      c = marksContract site "node";
    in
    builtins.seq (c.checked marks) (c.at marks);

  # The authority's operator is a gen-scope DOOR (a functor, den-hoag-7gp66 P2), so the reader is
  # the prelude's functor-aware one: `builtins.isFunction` reads a door as `false` and would refuse
  # the real authority.
  publishesResolve = e: builtins.isAttrs e && e ? resolve && prelude.isFunction e.resolve;
  noResolve =
    site: what:
    refuse site "field 'engine' must be a query authority publishing a 'resolve'; it is the injected membership authority, and this construct performs no ${what} of its own";

  importsLabel = "imports";
  parentLabel = "parent";

  # The three discipline flags, in their checked order. A list rather than three hand-written
  # branches, so the refusal names WHICH flag without three near-copies of one message.
  flagFields = [
    "localShadowsImport"
    "transitiveImports"
  ];

  # ★★ THE FLAG PAIR NAMES A PRESET; IT DECIDES NOTHING HERE (den-hoag-gayc design §2, the flag
  # table). `transitiveImports` picks the well-formedness (`parent* imports?` or `parent* imports*`),
  # `localShadowsImport` the label order (`neron`'s D < I < P, or I < D < P: `$` ranked strictly
  # between `imports` and `parent` through an empty middle rank). Every value is the authority's
  # own constructor's, so the order and the walk stay the delegate's. Any other order is stated
  # through the authority's `resolve` and `labelOrder` directly.
  presetOf = e: a: {
    wf =
      if a.transitiveImports then
        e.wellFormed {
          alphabet = [
            parentLabel
            importsLabel
          ];
          expression = "parent* imports*";
        }
      else
        e.neron.wf;
    order =
      if a.localShadowsImport then
        e.neron.order
      else
        e.labelOrder {
          alphabet = [
            parentLabel
            importsLabel
          ];
          layers = [
            [ importsLabel ]
            [ ]
            [ parentLabel ]
          ];
          endOfPath = 1;
        };
  };

  # The competition key: ONE declared constant, so every candidate competes and the selection
  # stays lazy in the data it shadows (gen-scope C1).
  group = "·";

  required = [
    # The injected query authority. Refused by name when it publishes no `resolve`, so a wrong
    # authority is loud at construction.
    "engine"
    # The name of the result — the attribute the evaluator binds it under.
    "name"
    # σ — the admission half of the defining query.
    "wellFormed"
    # π — the projection half: what the view carries from the resolved node.
    "project"
    # The boundary marks at each node (ADR-0026), `nodeId → [ { name; admits; } ]`, handed to the
    # authority as `bound`. REQUIRED, and "no marks" is `_: [ ]` written down: a defaulted
    # accessor is the query-property boundary ADR-0026 rejects, where silence becomes access.
    "marks"
  ]
  ++ flagFields;

  referenceResolution =
    args:
    let
      a = fields "referenceResolution" required args;

      badFlags = filter (f: !(builtins.isBool a.${f})) flagFields;
      marks = marksAt "referenceResolution" a.marks;
      record =
        self: id:
        a.engine.resolve (
          presetOf a.engine a
          // {
            mode = "visible";
            dataFilter = filterOver "referenceResolution" a;
            inherit group;
            bound = marks;
          }
        ) self id;
    in
    if !(publishesResolve a.engine) then
      noResolve "referenceResolution" "resolution"
    else if !(builtins.isString a.name) || a.name == "" then
      refuse "referenceResolution" "field 'name' must be the non-empty name of the result, which is the attribute the evaluator binds it under"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "referenceResolution" "field 'wellFormed' must be a predicate on the authority's node record; it is σ, the half of the defining query that decides whether a node's datum is a binding at all"
    else if !(builtins.isFunction a.project) then
      refuse "referenceResolution" "field 'project' must be a function from the authority's node record to the datum this view carries; it is π, and it is a field of its own because a predicate that also projects cannot be split into the two operators"
    else if badFlags != [ ] then
      refuse "referenceResolution" "field '${head badFlags}' is ${renderValue a.${head badFlags}}, which is not a boolean; the shadowing discipline and the import closure are DECLARED here rather than left to the authority's defaults"
    else
      builtins.seq marks {
        __element = "referenceResolution";
        inherit (a)
          name
          wellFormed
          project
          marks
          localShadowsImport
          transitiveImports
          ;

        # ★★★ THE COMPUTE IS DELEGATION AND NOTHING ELSE: the authority's visible selection under
        # the preset the flags name, one competition key, and `single`, which answers the one
        # declaration or refuses AMBIGUITY by name. σ and π are the `dataFilter`; the marks are
        # `bound`.
        compute = self: id: (record self id).single group;

        # ADR-0026's diagnostic: the edges the marks withheld at a node, each naming its marks —
        # the authority's own `withheld`, over the walk from that node.
        withheld = self: id: (record self id).withheld id;
      };

  reverseRequired = [
    # The injected query authority, refused by name when it publishes no `resolve`.
    "engine"
    # The name of the result — the attribute the evaluator binds it under.
    "name"
    # σ — the admission half of the defining query.
    "wellFormed"
    # π — the projection half: what the view carries from each contributing node.
    "project"
    # The boundary marks at each node, on the forward half's terms: REQUIRED, `_: [ ]` for none.
    "marks"
    # Direct importers, or the reverse-import closure: `imports` or `imports imports*` over the
    # converse.
    "transitive"
  ];

  # The converse's well-formedness: one `imports` step, or the closure.
  reverseWf =
    e: transitive:
    e.wellFormed {
      alphabet = [ importsLabel ];
      expression = if transitive then "imports imports*" else "imports";
    };

  neededBy =
    args:
    let
      a = fields "neededBy" reverseRequired args;
      marks = marksAt "neededBy" a.marks;
    in
    if !(publishesResolve a.engine) then
      noResolve "neededBy" "traversal"
    else if !(builtins.isString a.name) || a.name == "" then
      refuse "neededBy" "field 'name' must be the non-empty name of the result, which is the attribute the evaluator binds it under"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "neededBy" "field 'wellFormed' must be a predicate on the authority's node record; it is σ, the half of the defining query that decides whether an importer contributes at all"
    else if !(builtins.isFunction a.project) then
      refuse "neededBy" "field 'project' must be a function from the authority's node record to the datum this view carries; it is π, and it is a field of its own because a predicate that also projects cannot be split into the two operators"
    else if !(builtins.isBool a.transitive) then
      refuse "neededBy" "field 'transitive' is ${renderValue a.transitive}, which is not a boolean; the reverse-import closure is DECLARED here rather than left to the authority's default"
    else
      builtins.seq marks {
        __element = "neededBy";
        inherit (a)
          name
          wellFormed
          project
          marks
          transitive
          ;

        # ★★★ THE COMPUTE IS DELEGATION AND NOTHING ELSE — the authority's `witnesses` over the
        # converse, one answer per acyclic reverse path, in the authority's order. ★★ THE MARKS ARE
        # READ AT THE AUTHORED SOURCE: the converse is taken after the marks are applied (ADR-0024),
        # so an importer `o`'s edge `o → t` is withheld by `o`'s marks, exactly as
        # `referenceResolution` at `o` reads it — `t` is needed by `o` iff `o` reads `t`.
        compute =
          self: t:
          map (x: x.value)
            (a.engine.resolve {
              wf = reverseWf a.engine a.transitive;
              mode = "witnesses";
              direction = "inbound";
              dataFilter = filterOver "neededBy" a;
              bound = marks;
            } self t).answers;

        # The diagnostic at `t`: each DIRECT importer `o` whose edge to `t` the marks withheld,
        # `from = o` beside the authority's entry, naming the blocking marks. The authority keys an
        # inbound `withheld` at the AUTHORED source, so every node is asked; a non-importer has none.
        withheld =
          self: t:
          let
            r = a.engine.resolve {
              wf = reverseWf a.engine false;
              direction = "inbound";
              dataFilter = _: null;
              bound = marks;
            } self t;
          in
          concatMap (
            o: map (w: w // { from = o; }) (filter (w: w.label == importsLabel && w.target == t) (r.withheld o))
          ) self.allNodeIds;
      };
in
{
  inherit
    referenceResolution
    required
    neededBy
    reverseRequired
    ;
}
