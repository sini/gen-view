# THE RAW CALCULUS — five first-class carrier elements, each a NAMED EXPORT.
#
# ★★ WHY THE RAW LAYER IS PUBLISHED AND NOT ONLY THE COMPOSITIONS. A library publishing only its
# convenience composition HIDES the calculus, so a consumer needing a different instance has to
# re-implement one. Two measured instances of exactly that sit in this ecosystem: gen-select's
# `matchView` is unexported while `sel = select;` is exported, and `setAttrByPath` has no exported
# home anywhere and three private twins. Both are raw primitives trapped inside composition-only
# libraries, and both are why those constructs have no home to retire into.
#
# ★★ AND HERE THE RULE IS DOUBLY LOAD-BEARING. The CONSTRUCTS of this library migrate into a
# consolidated library later; the CONTAINER does not. So construct boundaries carry all of the
# design weight and the container carries none: a published calculus moves intact, where a
# composition-only surface would have to be rebuilt at the fold.
#
# ── THEORY ────────────────────────────────────────────────────────────────────────────────────
# van Antwerpen, Poulsen, Rouvoet & Visser 2018, "Scopes as Types", Fig. 1, printed 114:5:
#
#   Syntax Parameters      data terms  d ∈ D   "a set of data terms"
#                          labels      l ∈ L   "a set of edge labels"
#                          relations   r ∈ R   "a set of relation names"
#   Syntax Definitions     scope graphs G ∈ Graphs ::= ⟨scopes ⊆ S, edges ⊆ Edges, data ⊆ Data⟩
#                          extended labels l̂ ∈ L̂ := L ∪ {$}, "where $ indicates the end of a path"
#   Visibility Parameters  data term well-formedness  WFD ⊆ D
#                          label well-formedness      WFL ⊆ L*  "defined as a regular expression"
#                          data order                 ≤d ⊆ D × D   partial order
#                          label order                <l ⊆ L̂ × L̂   strict partial order
#
# gen's carrier is a NARROWING of that figure, not an extension of it: `follow` is WFL, the label
# ranking is <l, the competition key is an instance of ≤d, and WFD ships in gen as the `where`
# predicate without being named a carrier parameter at all. gen therefore names one visibility
# parameter FEWER than the paper defines — and was missing a SYNTAX parameter outright, the
# relation sort R, which this file publishes.
#
# ★ THE RELATION SORT IS PUBLISHED AS A FIRST-CLASS CARRIER ELEMENT, and that is an obligation
# rather than a design choice made here. Under the scoped-relations arrangement — van Antwerpen
# 2018's own — `relations r ∈ R` is a SYNTAX parameter, datums are a separate sort
# (`Data ::= s —r→ d`), and the relation is reached ONCE, AT THE END of the path, by (NR-Rel):
# from `G ⊢ p : s ↠ s′` and `s′ —r→ d ∈ data(G)` with `WFL ⊢ p ok` and `d ∈ WFD`, conclude
# `WFD, WFL, G ⊢ p : s —r→ d`. ⇒ THE WALK IS STRUCTURAL THROUGHOUT and content is filtered by WFD
# at the end, so A CONTENT NAME CAN NEVER ENTER THE LABEL WORD. That is why `edgeLabels` below is
# structural-only and why `carrier` refuses an overlap between the alphabet and the relation names.
#
# ★ ACQUISITION GAP, recorded rather than papered over: no paper has a general noun for a
# "structural relay letter" — they name only the parent edge `P`. None is invented here.
{ prelude, graph }:
let
  inherit (prelude)
    all
    any
    concatMap
    elem
    filter
    foldl'
    head
    length
    map
    sort
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    strings
    quote
    ;

  # A label is a word in gen-graph's parse alphabet. This is not decoration: `regex.stateKey`
  # renders a composite with `* | . ( )`, so a label carrying one of those can collide with a
  # composite's canonical rendering and two dissimilar derivative states can share a seen-key.
  # The constructor owns the constraint because it is the only place that sees the whole set.
  isLabelChar =
    c:
    (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || (c >= "0" && c <= "9") || c == "_" || c == "-";
  isLabelWord =
    s:
    let
      n = builtins.stringLength s;
    in
    n > 0 && all (i: isLabelChar (builtins.substring i 1 s)) (builtins.genList (i: i) n);

  # ── L — the STRUCTURAL-ONLY label alphabet ─────────────────────────────────────────────────
  # Fig. 1: `labels l ∈ L`, "a set of edge labels". Structural-only is the Q21 consequence: a
  # content name lives in R and is reached at the terminus, never stepped through, so it is not
  # a letter and cannot be one.
  #
  # `$` IS NOT A LETTER AND IS NOT DECLARED. The extended alphabet L̂ := L ∪ {$} is DERIVED here
  # rather than written by the caller, because `$` "indicates the end of a path" and is therefore
  # a property of every alphabet rather than a choice about one. `_` is likewise refused: it is
  # gen-graph's any-label wildcard in the parse grammar, so a letter spelled `_` would be
  # unaddressable in every expression written over this alphabet.
  edgeLabels =
    args:
    let
      a = fields "edgeLabels" [ "letters" ] args;
      letters = strings "edgeLabels" "letters" a.letters;
      reserved = filter (l: l == "_" || l == "$") letters;
      malformed = filter (l: !(isLabelWord l)) letters;
    in
    if letters == [ ] then
      refuse "edgeLabels" "letters is empty; an alphabet with no letters admits no path, so every view over it is empty and nothing says why"
    else if reserved != [ ] then
      refuse "edgeLabels" "letter '${head reserved}' is reserved — `_` is the any-label wildcard of the path-expression grammar and `$` is the extended label marking the end of a path (van Antwerpen 2018 Fig. 1); neither can also name an edge"
    else if malformed != [ ] then
      refuse "edgeLabels" "letter '${head malformed}' is outside the label word alphabet [A-Za-z0-9_-]+; a letter carrying an expression metacharacter can collide with a composite's canonical rendering in the derivative state key"
    else
      {
        __element = "edgeLabels";
        inherit letters;
        # L̂ := L ∪ {$}. Derived, never declared.
        extended = letters ++ [ "$" ];
        member = l: elem l letters;
      };

  # ── R — the relation sort ───────────────────────────────────────────────────────────────────
  # Fig. 1: `relations r ∈ R`, "a set of relation names". A SYNTAX parameter, like L, and unlike L
  # it carries NO lexical constraint — precisely because a relation name never enters the label
  # word. It is reached at the path's end by (NR-Rel) and nowhere else, so nothing ever renders it
  # into a derivative state key.
  #
  # ★ THE ARRANGEMENT IS WHAT MAKES A CONTAINMENT RELAY FALL OUT rather than be added. An
  # admission alphabet made entirely of binding-kinds sits in a substrate position with no
  # structural letter, which is what forces one content symbol to double as the ancestor relay.
  # Splitting the sorts removes the pressure; adding a fifth STRUCTURAL letter instead reproduces
  # the earlier arrangement that the scoped-relations form is a published simplification of.
  relations =
    args:
    let
      a = fields "relations" [ "names" ] args;
      names = strings "relations" "names" a.names;
    in
    if names == [ ] then
      refuse "relations" "names is empty; a carrier with no relation sort can reach no datum, and (NR-Rel) is the only rule by which a view reaches content"
    else
      {
        __element = "relations";
        inherit names;
        member = r: elem r names;
      };

  # ── E — label well-formedness ───────────────────────────────────────────────────────────────
  # Fig. 1: `WFL ⊆ L*`, "defined as a regular expression". The expression is stepped by
  # Brzozowski (1964) derivatives held in a normal form, so the derivative state set is finite and
  # a cyclic graph terminates — Brzozowski Thm 5.2, over the similarity of his Def 5.2, whose
  # ACI identities of ALTERNATION the normalization must PERFORM rather than merely satisfy
  # ("it is the identity R + R = R which allows us to terminate the process", Appendix II).
  # gen-graph's `regex` is that kernel and is CITED HERE RATHER THAN REINVENTED.
  #
  # ★ EVERY LITERAL IS CHECKED AGAINST THE ALPHABET, and that check is what makes "a content name
  # can never enter the label word" true BY CONSTRUCTION rather than by discipline. Without it a
  # relation name — or a relatum-role label, a third population that indexes nothing in this
  # carrier — could be written into an expression, and the walk would simply never match it: a
  # silent empty answer where a refusal belongs.
  labelWellFormedness =
    args:
    let
      a = fields "labelWellFormedness" [
        "alphabet"
        "expression"
      ] args;
      alphabet = elementOf "labelWellFormedness" "alphabet" "edgeLabels" a.alphabet;
      expr = graph.regex.parse a.expression;
      literalsOf =
        r:
        if r.t == "lit" then
          [ r.l ]
        else if r.t == "star" then
          literalsOf r.r
        else if r.t == "seq" || r.t == "alt" then
          concatMap literalsOf r.rs
        else
          [ ];
      literals = literalsOf expr;
      foreign = filter (l: !(alphabet.member l)) literals;
    in
    if foreign != [ ] then
      refuse "labelWellFormedness" "the expression names '${head (sort builtins.lessThan foreign)}', which is not a letter of the alphabet (${quote alphabet.letters}); a path expression ranges over L and a name outside it would match nothing and say nothing"
    else
      {
        __element = "labelWellFormedness";
        inherit alphabet literals expr;
        inherit (a) expression;
        # The three operations a walk needs, so a caller stepping the policy itself never has to
        # reach past this element into the regex kernel.
        step = label: state: graph.regex.deriv label state;
        accepts = state: graph.regex.nullable state;
        stateKey = state: graph.regex.stateKey state;
      };

  # ── < — the label order ─────────────────────────────────────────────────────────────────────
  # Fig. 1: `<l ⊆ L̂ × L̂`, a STRICT PARTIAL ORDER over the EXTENDED alphabet. The declaration is a
  # list of LAYERS, most-specific first: layer 0 outranks layer 1, and two letters in one layer
  # are incomparable. Layers rather than a flat list is what keeps this a partial order — a flat
  # list can only express a total one, and "no specificity at all" would then be inexpressible
  # except by accident.
  #
  # ★★ THE RANKING IS TOTAL OVER L̂, AND AN OMITTED LETTER IS REFUSED BY NAME. The shipped
  # precedent this corrects ranks an unlisted label at `length labels` — a silent default that
  # makes every unranked letter tie at the bottom, so a caller who forgets one gets an order that
  # answers rather than one that objects. `$` is ranked by its own required field because the
  # end-of-path rank decides whether stopping outranks continuing, which is a per-query decision
  # and not a property of the alphabet.
  #
  # THE LIFT. `pathPrecedes` compares two witness paths lexicographically on their rank words;
  # when one word is exhausted its END-OF-PATH rank competes against the other word's next label
  # rank. A low `endOfPath` makes stopping outrank everything, so a proper prefix beats its own
  # extensions; a higher one lets continuation on lower-ranked labels beat stopping.
  labelOrder =
    args:
    let
      a = fields "labelOrder" [
        "alphabet"
        "layers"
        "endOfPath"
      ] args;
      alphabet = elementOf "labelOrder" "alphabet" "edgeLabels" a.alphabet;
      layers = a.layers;
      # `strings` runs HERE, on the flattened declaration, so a letter ranked twice is refused by
      # name rather than silently taking whichever layer the fold visited last.
      flat = strings "labelOrder" "layers" (concatMap (l: l) layers);
      missing = filter (l: !(elem l flat)) alphabet.letters;
      foreign = filter (l: !(alphabet.member l)) flat;
      ranks = foldl' (
        acc: i:
        acc
        // builtins.listToAttrs (
          map (l: {
            name = l;
            value = i;
          }) (builtins.elemAt layers i)
        )
      ) { } (builtins.genList (i: i) (length layers));
      rankOf = l: if l == "$" then a.endOfPath else ranks.${l};
    in
    if !(builtins.isList layers) || any (l: !(builtins.isList l)) layers then
      refuse "labelOrder" "layers must be a list of lists — each inner list is one rank, and two letters sharing a rank are incomparable, which is how a strict PARTIAL order is declared"
    else if !(builtins.isInt a.endOfPath) then
      refuse "labelOrder" "endOfPath must be an int; it is the rank of the extended label `$` and decides whether stopping outranks continuing"
    else if foreign != [ ] then
      refuse "labelOrder" "layers rank '${head (sort builtins.lessThan foreign)}', which is not a letter of the alphabet (${quote alphabet.letters})"
    else if missing != [ ] then
      refuse "labelOrder" "letter '${head (sort builtins.lessThan missing)}' is not ranked; the label order is total over the alphabet, and an unranked letter would otherwise take a default rank nobody declared"
    else
      {
        __element = "labelOrder";
        inherit alphabet layers rankOf;
        inherit (a) endOfPath;
        # `<l` itself: the strict partial order over L̂ the figure defines. Two letters of one
        # layer are incomparable, so neither precedes the other.
        precedes = x: y: rankOf x < rankOf y;
        rankWord = path: map (step: rankOf step.label) path;
        # The lexicographic lift over rank words, with the end-of-path rank at exhaustion.
        pathPrecedes =
          pa: pb:
          let
            wa = map (step: rankOf step.label) pa;
            wb = map (step: rankOf step.label) pb;
            la = length wa;
            lb = length wb;
            go =
              i:
              if i >= la && i >= lb then
                false
              else if i >= la then
                a.endOfPath < builtins.elemAt wb i
              else if i >= lb then
                builtins.elemAt wa i < a.endOfPath
              else if builtins.elemAt wa i < builtins.elemAt wb i then
                true
              else if builtins.elemAt wa i > builtins.elemAt wb i then
                false
              else
                go (i + 1);
          in
          go 0;
      };

  # ── k — the competition key, an instance of the data order ──────────────────────────────────
  # Fig. 1: `data order ≤d ⊆ D × D`, a partial order. gen's instance is a GROUPING: contributions
  # sharing a key compete, contributions with different keys do not — the incomparability classes
  # of the order, read as the unit of competition.
  #
  # ★★ BOTH FIELDS ARE REQUIRED AND NEITHER IS DEFAULTED. The measured defect this corrects is a
  # per-node default grouping, under which competition is VACUOUS: a chain returns the gather-all
  # answer with nothing shadowed, while the same query with the key written returns one visible
  # contribution and one shadowed. THE FIX IS A MANDATORY KEY, NOT A DIFFERENT DEFAULT — a
  # carrier built on defaults inherits vacuity at the foundation, and the next default is as
  # arbitrary as the last.
  #
  # `channel` is simultaneously the NAME OF THE RESULT and the unit of competition at the
  # composition surface, where `keyOf` is derived from it. At this raw layer the two are separate
  # fields, because a registry competes per entity and a channel competes per channel, and a
  # calculus that could only say one of those would hide the other.
  #
  # ★ AN OPEN FORK RIDES ON THIS ELEMENT AND IS NOT SETTLED HERE: whether `channel` collapses
  # into the relation sort `r`. A second reading of the same surface holds that the competition
  # key stands in for the relation the query is ABOUT and that this is why it had to be invented
  # at all. This library builds `r` as a first-class element and leaves the key where the ruling
  # puts it — the only arm that presupposes NEITHER answer.
  dataOrder =
    args:
    let
      a = fields "dataOrder" [
        "channel"
        "keyOf"
      ] args;
    in
    if !(builtins.isString a.channel) || a.channel == "" then
      refuse "dataOrder" "channel must be a non-empty string; it names the result, and an unnamed result cannot be read back or refused by name"
    else if !(builtins.isFunction a.keyOf) then
      refuse "dataOrder" "keyOf must be a function from a contribution to its competition key; it is required and total, because a defaulted key makes competition vacuous rather than absent"
    else
      {
        __element = "dataOrder";
        inherit (a) channel keyOf;
      };

  # `elementOf site field element value` — a carrier element is a CONSTRUCTED value, and a check
  # that it is the right one is what stops a plain attrset with the right attribute names being
  # accepted for it. Declared here rather than in refusal.nix because the tag is this file's.
  elementOf =
    site: field: element: value:
    if builtins.isAttrs value && (value.__element or null) == element then
      value
    else
      refuse site "field '${field}' is not a ${element} carrier element (found ${
        if builtins.isAttrs value then
          "an attrset tagged ${builtins.toJSON (value.__element or null)}"
        else
          "a ${builtins.typeOf value}"
      }); build it with `${element}` so the element's own refusals have already run";

  # ── THE CARRIER — the five elements assembled, with the cross-checks no element can make alone
  # Each element validates itself; only the assembly can see whether they are about the same
  # alphabet and whether the structural and content populations overlap.
  carrier =
    args:
    let
      a = fields "carrier" [
        "labels"
        "labelWellFormedness"
        "labelOrder"
        "dataOrder"
        "relations"
      ] args;
      labels = elementOf "carrier" "labels" "edgeLabels" a.labels;
      wfl = elementOf "carrier" "labelWellFormedness" "labelWellFormedness" a.labelWellFormedness;
      ord = elementOf "carrier" "labelOrder" "labelOrder" a.labelOrder;
      key = elementOf "carrier" "dataOrder" "dataOrder" a.dataOrder;
      rels = elementOf "carrier" "relations" "relations" a.relations;
      # ★ THE Q21 DISJOINTNESS. A name in both populations would let an admission expression name
      # content, which is exactly the arrangement the scoped-relations split exists to remove.
      overlap = filter (r: labels.member r) rels.names;
    in
    if wfl.alphabet.letters != labels.letters then
      refuse "carrier" "labelWellFormedness is built over a different alphabet than `labels` (${quote wfl.alphabet.letters} vs ${quote labels.letters}); one carrier has one L"
    else if ord.alphabet.letters != labels.letters then
      refuse "carrier" "labelOrder is built over a different alphabet than `labels` (${quote ord.alphabet.letters} vs ${quote labels.letters}); one carrier has one L"
    else if overlap != [ ] then
      refuse "carrier" "'${head (sort builtins.lessThan overlap)}' is both a letter of L and a name in R; the sorts are disjoint, because the walk steps only on structural letters and a content name reached at the path's end can never enter the label word"
    else
      {
        __element = "carrier";
        inherit labels;
        relations = rels;
        labelWellFormedness = wfl;
        labelOrder = ord;
        dataOrder = key;
      };

  # ── THE SCOPE GRAPH — ⟨scopes, edges, data⟩ ────────────────────────────────────────────────
  # Fig. 1's Syntax Definitions, built whole: `scopes ⊆ S`, `edges ⊆ Edges` where
  # `Edges ::= s —l→ s`, and `data ⊆ Data` where `Data ::= s —r→ d`. The data component is a
  # SEPARATE SORT and not an edge payload, which is the whole content of the scoped-relations
  # arrangement.
  #
  # ★★ `data` TAKES THE GRAPH, AND THAT IS THE ONE DELIBERATE DIVERGENCE FROM THE FIGURE.
  # In the calculus `data(G)` is a COMPONENT of G and therefore walk-independent by definition —
  # a datum is in it or it is not, and no traversal can put one there. In a substrate where the
  # component is reached through an accessor, walk-dependence becomes SAYABLE: an accessor can
  # consult the graph and re-emit, at one scope, datums it found by walking out of it. Taking the
  # graph as a parameter is what makes that possible shape VISIBLE to the substrate instead of
  # leaving it to arrive undetected — see `arrival.nix`, which derives which of the two happened
  # and restores the calculus's own property by construction.
  #
  # EVERY EDGE LABEL IS CHECKED AGAINST L at construction. A third population exists at the
  # boundary — the relatum-role labels of a reified relation — and it indexes NOTHING in this
  # carrier: its intersection with L is empty, so the derivative of any admission expression on
  # one of those labels is the empty state and the walk cannot enter a binding at all.
  scopeGraph =
    args:
    let
      a = fields "scopeGraph" [
        "carrier"
        "scopes"
        "edges"
        "data"
      ] args;
      c = elementOf "scopeGraph" "carrier" "carrier" a.carrier;
      scopes = strings "scopeGraph" "scopes" a.scopes;
      edgeLabelNames = builtins.attrNames a.edges;
      foreign = filter (l: !(c.labels.member l)) edgeLabelNames;
      labeled = graph.labeledFrom {
        perLabel = a.edges;
        nodes = scopes;
      };
    in
    if !(builtins.isAttrs a.edges) then
      refuse "scopeGraph" "edges must be an attrset of label → (scope → [ scope ]); it is the per-label accessor the walk steps"
    else if !(builtins.isFunction a.data) then
      refuse "scopeGraph" "data must be a function of the graph — `labeledGraph → scope → [ { relation; datum; } ]`; it is the ⟨scopes, edges, data⟩ triple's third component"
    else if foreign != [ ] then
      refuse "scopeGraph" "edges carry the label '${head (sort builtins.lessThan foreign)}', which is not a letter of L (${quote c.labels.letters}); the walk steps only on structural letters"
    else
      {
        __element = "scopeGraph";
        carrier = c;
        inherit scopes labeled;
        inherit (a) edges data;
      };

  # ── (NR-Rel) — the relation is reached ONCE, AT THE END of the path ─────────────────────────
  # From `G ⊢ p : s ↠ s′` and `s′ —r→ d ∈ data(G)` with `WFL ⊢ p ok` and `d ∈ WFD`, conclude
  # `WFD, WFL, G ⊢ p : s —r→ d`. This binding is the second premise and the conclusion's datum
  # component: given a reached scope, the relation and the data-term well-formedness predicate, it
  # yields the datums. The path premise belongs to the walk and is discharged there.
  #
  # ★ AN UNKNOWN RELATION IS REFUSED BY NAME rather than yielding the empty list, because the two
  # are indistinguishable in an answer and must not be indistinguishable in a diagnostic: a
  # misspelled relation that gathered nothing looks exactly like a relation with no datums.
  #
  # ★ `data` IS APPLIED TO THE GRAPH THE CALLER HANDS IN, never to a graph this binding chooses.
  # That is what lets `arrival.nix` pass a severed graph through the same rule and get the
  # walk-independent answer, with no second lookup path to keep in step with this one.
  relationLookup =
    args:
    let
      a = fields "relationLookup" [
        "graph"
        "labeled"
        "scope"
        "relation"
        "wellFormed"
      ] args;
      g = elementOf "relationLookup" "graph" "scopeGraph" a.graph;
    in
    if !(g.carrier.relations.member a.relation) then
      refuse "relationLookup" "'${a.relation}' is not a name in R (${quote g.carrier.relations.names}); an undeclared relation is refused rather than answered empty, because an empty answer cannot be told from a relation with no datums"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "relationLookup" "wellFormed must be a predicate on data terms; it is WFD, the visibility parameter that decides whether the datum found at the path's end is the one being looked for"
    else
      map (entry: entry.datum) (
        filter (entry: entry.relation == a.relation && a.wellFormed entry.datum) (g.data a.labeled a.scope)
      );
in
{
  inherit
    edgeLabels
    relations
    labelWellFormedness
    labelOrder
    dataOrder
    carrier
    scopeGraph
    relationLookup
    elementOf
    ;
}
