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
# words belongs to the delegate. The compute is `engine.query { … }` and nothing else, so a change
# at the delegate arrives here as a change in BEHAVIOUR rather than as a divergence between two
# implementations of one mechanism. A later author who "optimizes" a shadowing decision into this
# file has built a second resolution implementation, and the delegation oracle is what fails then.
#
# ★★ THE DISPOSAL OF A MULTI-CANDIDATE IMPORT SET IS THE DELEGATE'S TOO — POINTED AT, NEVER
# RESTATED HERE. D < I < P orders the three SORTS; nothing in Fig. 2 orders candidates AMONG the
# imports. gen-scope's `query` disposes such a set BY THE RUNTIME TYPE OF THE PROJECTED DATUM: an
# attrset folds a shadow across EVERY candidate, anything else takes the first in traversal order,
# and that order is the caller's own DECLARED imports list — documented there, and nowhere claimed
# as a precedence rule. ⇒ THE CARDINALITY IS ONE AND THE PROVENANCE IS NOT. Exactly one value (or
# `null`) comes back, so `null` remains the delegate's "no visible binding" answer and never an
# empty gather — but THE VALUE IS NOT IN GENERAL THE DATUM OF ANY ONE NODE, and Néron rule (X)
# derives one declaration where this derives one DISPOSAL.
#
# ★★★ WHICH IS WHY THERE IS NO `codomain` FIELD, AND THE REASON IS WORTH MORE THAN THE FIELD WAS. A
# literal such as `codomain = "atMostOne"` written HERE would be a constant about a fact owned
# THERE — false in the form it claims, and derived by nothing. The disposal is selected inside the
# delegate's closure on the runtime type of a value this construct's own `project` produces: no
# constructor can inspect a closure's branch, and no construction-time check can know the type of a
# datum that does not exist until the query runs. The fact is therefore not derivable, so it is not
# published as a field — it is POINTED AT, above. Nothing that could go stale is written down.
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
# value publishing no `query` is refused BY NAME at construction rather than at some later force.
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
# ★★ THE INVERSE IS COMPUTED BY ENUMERATION, NEVER BY A TRANSPOSE, AND THE WORD MATTERS AT THIS
# SEAM. The delegate reaches an id's importers by a FILTER OVER THE NODE SET, and it holds no
# transpose at all. Meanwhile "labelled transpose" names exactly one thing in this library —
# `viewRelation`'s inbound arm — so borrowing the term here would point a later author at
# `graph.labeledTranspose` and put a transpose INSIDE a construct whose whole design is that it
# holds none. The *labelled* qualifier would earn nothing either: it exists because that walk
# crosses a multi-label graph, and this delegate has one relation and no label component to
# preserve.
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
# ★★ THE CLAIMED-FROM-NO-PAPER DISCLOSURE IS INHERITED AND IS NEVER DROPPED. The delegate's own
# reverse operator records that it is that library's OWN dual, claimed from no paper, and that the
# citation it used to carry was measured FALSE at the primary. This construct inherits the
# disclosure and not the citation.
#
# ── WHAT IS DELIBERATELY NOT A FIELD HERE ────────────────────────────────────────────────────
# THE SHADOWING FLAGS. There is no shadowing in a gather — D < I < P orders SORTS of candidate and
# a reverse gather has exactly one sort — and the delegate refuses the forward names loudly, in a
# way `tryEval` cannot catch.
#
# A `dedup` OR AN ORDER. `viewDefinition` requires both because it holds a competition; this
# construct holds none, and a fold written here would be this library implementing one the
# delegate owns.
#
# A `codomain`, A `relation` AND A `root`, each declined for the forward half's own reason, one
# relation over.
{ prelude }:
let
  inherit (prelude) filter head;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal) refuse fields;

  # ── THE TWO HELPERS BOTH CONSTRUCTS SHARE, AT MODULE SCOPE ───────────────────────────────────
  # ★★ ONE GUARD FOR ONE DELEGATE CONVENTION, WHICH IS WHY IT IS LIFTED RATHER THAN COPIED. The
  # null-projection guard states ONE fact about ONE authority — that it reads `null` as NO BINDING
  # HERE — and both of that authority's operators hold it: `queryReverse` DROPS a null contribution
  # exactly as `query` reads one as an absent binding. Two copies in two `let`s would be two
  # statements of one fact, which is the drift class this file declines a `relation` field over.

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
  # operators, so one message states one fact. What differs between the two call sites is only
  # WHICH construct refused and under WHAT result name: the two coordinates a caller who meets this
  # while forcing an attribute far from the declaration cannot act without.
  requireNonNull =
    site: resultName: node: value:
    if value == null then
      refuse site "result '${resultName}': node ${nodeLabel node} is admitted by 'wellFormed' and its 'project' returned null; the query authority reads null as NO BINDING HERE, so a null projection would be indistinguishable from an absent one"
    else
      value;

  # The three discipline flags, in their checked order. A list rather than three hand-written
  # branches, so the refusal names WHICH flag without three near-copies of one message.
  flagFields = [
    "localShadowsImport"
    "importShadowsParent"
    "transitiveImports"
  ];

  required = [
    # The injected query authority. Refused by name when it publishes no `query`, so a wrong
    # authority is loud at construction.
    "engine"
    # The name of the result — the attribute the evaluator binds it under.
    "name"
    # σ — the admission half of the defining query.
    "wellFormed"
    # π — the projection half: what the view carries from the resolved node.
    "project"
  ]
  ++ flagFields;

  referenceResolution =
    args:
    let
      a = fields "referenceResolution" required args;

      badFlags = filter (f: !(builtins.isBool a.${f})) flagFields;
    in
    if !(builtins.isAttrs a.engine) || !(a.engine ? query) then
      refuse "referenceResolution" "field 'engine' must be a query authority publishing a 'query'; it is the injected membership authority, and this construct performs no resolution of its own"
    else if !(builtins.isString a.name) || a.name == "" then
      refuse "referenceResolution" "field 'name' must be the non-empty name of the result, which is the attribute the evaluator binds it under"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "referenceResolution" "field 'wellFormed' must be a predicate on the authority's node record; it is σ, the half of the defining query that decides whether a node's datum is a binding at all"
    else if !(builtins.isFunction a.project) then
      refuse "referenceResolution" "field 'project' must be a function from the authority's node record to the datum this view carries; it is π, and it is a field of its own because a predicate that also projects cannot be split into the two operators"
    else if badFlags != [ ] then
      refuse "referenceResolution" "field '${head badFlags}' is ${
        builtins.toJSON a.${head badFlags}
      }, which is not a boolean; the shadowing discipline and the import closure are DECLARED here rather than left to the authority's defaults"
    else
      {
        __element = "referenceResolution";
        inherit (a)
          name
          wellFormed
          project
          localShadowsImport
          importShadowsParent
          transitiveImports
          ;

        # ★★★ THE COMPUTE IS DELEGATION AND NOTHING ELSE. Every parameter the authority would
        # otherwise default is passed from the declaration, so the declaration determines its own
        # defining query rather than inheriting a discipline nobody wrote down.
        compute = a.engine.query {
          dataFilter =
            n: if a.wellFormed n then requireNonNull "referenceResolution" a.name n (a.project n) else null;
          inherit (a) localShadowsImport importShadowsParent transitiveImports;
        };
      };

  reverseRequired = [
    # The injected query authority. Refused by name when it publishes no `queryReverse` — NOT
    # `query`: an authority offering only the forward operator cannot answer this construct, and a
    # check copied from the sibling above would accept it and then fail at force with an unnamed
    # error.
    "engine"
    # The name of the result — the attribute the evaluator binds it under.
    "name"
    # σ — the admission half of the defining query.
    "wellFormed"
    # π — the projection half: what the view carries from each contributing node.
    "project"
    # Direct importers, or the reverse-import closure. Named for the DELEGATE'S formal so that
    # `inherit (a) transitive` passes it and a disagreement between two written-down literals is
    # inexpressible rather than merely unlikely.
    "transitive"
  ];

  neededBy =
    args:
    let
      a = fields "neededBy" reverseRequired args;
    in
    if !(builtins.isAttrs a.engine) || !(a.engine ? queryReverse) then
      refuse "neededBy" "field 'engine' must be a query authority publishing a 'queryReverse'; it is the injected membership authority, and this construct performs no traversal of its own — an authority publishing only the forward 'query' cannot answer the reverse direction"
    else if !(builtins.isString a.name) || a.name == "" then
      refuse "neededBy" "field 'name' must be the non-empty name of the result, which is the attribute the evaluator binds it under"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "neededBy" "field 'wellFormed' must be a predicate on the authority's node record; it is σ, the half of the defining query that decides whether an importer contributes at all"
    else if !(builtins.isFunction a.project) then
      refuse "neededBy" "field 'project' must be a function from the authority's node record to the datum this view carries; it is π, and it is a field of its own because a predicate that also projects cannot be split into the two operators"
    else if !(builtins.isBool a.transitive) then
      refuse "neededBy" "field 'transitive' is ${builtins.toJSON a.transitive}, which is not a boolean; the reverse-import closure is DECLARED here rather than left to the authority's default"
    else
      {
        __element = "neededBy";
        inherit (a)
          name
          wellFormed
          project
          transitive
          ;

        # ★★★ THE COMPUTE IS DELEGATION AND NOTHING ELSE — the anti-drift condition above, one
        # relation over. Every parameter the authority would otherwise default is passed from the
        # declaration, so the declaration determines its own defining query rather than inheriting
        # a closure discipline nobody wrote down.
        compute = a.engine.queryReverse {
          dataFilter = n: if a.wellFormed n then requireNonNull "neededBy" a.name n (a.project n) else null;
          inherit (a) transitive;
        };
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
