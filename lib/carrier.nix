# THE RAW CALCULUS — five first-class carrier elements, each a NAMED EXPORT.
#
# ★★ WHY THE RAW LAYER IS PUBLISHED AND NOT ONLY THE COMPOSITIONS. A library publishing only its
# convenience composition HIDES the calculus, so a consumer needing a different instance has to
# re-implement one. Two measured instances of exactly that sat in this ecosystem: gen-select's
# `matchView` is unexported while `sel = select;` is exported, and `setAttrByPath` had no exported
# home anywhere and three private twins. Both are raw primitives trapped inside composition-only
# libraries, and both are why those constructs had no home to retire into.
#
# ★ THE SECOND INSTANCE IS DISCHARGED, AND HOW IT WAS IS THE POINT. This library's own reading was
# that the fix is to publish the primitive from HERE, and it did. The owner ruled otherwise
# (2026-08-27): it lands in the UTILITY BASE, and `setAttrByPath` + `getAttrByPath` shipped in
# gen-prelude with every live twin converging on them. What survives is the RULE — a raw primitive
# needs an exported home — and the ruling settled only WHICH library is that home. Publishing it
# from a placement library would have given the primitive an owner it does not belong to; the
# rejected position and its measurement are kept at `placement.nix`.
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
    any
    concatMap
    elem
    filter
    foldl'
    genAttrs
    head
    imap0
    length
    map
    sort
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  inherit (refusal)
    refuse
    fields
    decided
    returned
    formalsOf
    strings
    attrKey
    quote
    renderValue
    renderSubject
    sortNames
    ;

  # The three label populations' list laws (a letter is a label word; `_` and `$` are reserved;
  # R is non-empty) live in elements.nix as ONE definition, run here by each constructor and there
  # by the intake — the library decides membership by reading these lists and never through the
  # `member` each element publishes, so a forged list must meet the constructor's own law.
  inherit (import ./elements.nix { inherit prelude; })
    lettersLaw
    relationNamesLaw
    relatumNamesLaw
    ;

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
      letters = lettersLaw "edgeLabels" "letters" a.letters;
    in
    builtins.seq letters {
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
      names = relationNamesLaw "relations" "names" a.names;
    in
    builtins.seq names {
      __element = "relations";
      inherit names;
      member = r: elem r names;
    };

  # ── Λ — the RELATUM LABELS, a THIRD population, and NOT a carrier element ──────────────────
  # ★★★ IT IS NOT ONE OF THE FIVE, AND SAYING SO IS THE POINT. A binding is a NODE — a reified
  # relation identified by the labelled tuple of its relata — and its INCIDENT EDGES DO REACH THE
  # GRAPH'S EDGE SET, carrying the ROLES the relata play. Measured at the single edge-emission site
  # of the shipped minter, the emitted incidence label ranges over the relatum ROLES and never over
  # the relation name. So `Λ` is a real population of `labels(edges(G))` — and it INDEXES NOTHING
  # IN THE CARRIER: admission is indexed by the binding's KIND, the relation `r`, and never by a
  # role label. A carrier of six would be claiming the opposite.
  #
  # ★★ WHY IT MUST BE DECLARED RATHER THAN INFERRED AS "WHATEVER IS NOT IN L". The law is a
  # THREE-WAY condition — `L ∩ R = ∅`, `L ∩ Λ = ∅`, `R ∩ Λ = ∅`, and
  # `labels(edges(G)) ⊆ L ⊎ R ⊎ Λ`: disjoint AND jointly exhaustive, refused at construction. An
  # inferred `Λ = ¬L` makes `L ∩ Λ = ∅` true by construction and therefore UNFALSIFIABLE — the
  # collision the law exists to refuse becomes unstateable, and the exhaustiveness half becomes
  # vacuous because nothing can fall outside. A declared population is what makes both halves say
  # anything.
  #
  # ★★ AND THE INERTNESS IS STRUCTURAL, NOT PROMISED. A `Λ` label can appear in no path expression,
  # because `labelWellFormedness` refuses every literal outside `L` and `Λ ∩ L = ∅`. So the
  # Brzozowski derivative of ANY admission expression with respect to a role label is the empty
  # state, its canonical key is `"0"`, and the walk prunes there: **`Λ`-labelled edges are HELD AND
  # NOT WALKED** — present in the graph, invisible to WFL, read as datums by nothing. That is why
  # this population carries no lexical constraint of its own: a role label never enters an
  # expression, so it never renders into a derivative state key.
  #
  # ★ AN EMPTY `Λ` IS LAWFUL, WHERE AN EMPTY `R` IS NOT, AND THE ASYMMETRY IS NOT AN OVERSIGHT. R
  # empty means no datum is reachable at all, since (NR-Rel) is the only rule by which a view
  # reaches content. Λ empty means the graph holds no reified bindings — an ordinary graph, and the
  # commonest one. Refusing it would refuse every graph that has no relata to name.
  relatumLabels =
    args:
    let
      a = fields "relatumLabels" [ "names" ] args;
      names = relatumNamesLaw "relatumLabels" "names" a.names;
    in
    decided [ names ] {
      __element = "relatumLabels";
      inherit names;
      member = l: elem l names;
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
      expr = exprOf "labelWellFormedness" "" alphabet a.expression;
      literals = literalsOf expr;
    in
    builtins.seq expr (
      decided [ alphabet ] {
        __element = "labelWellFormedness";
        inherit alphabet literals expr;
        inherit (a) expression;
        # The three operations a walk needs, so a caller stepping the policy itself never has to
        # reach past this element into the regex kernel.
        step = label: state: graph.regex.deriv label state;
        accepts = state: graph.regex.nullable state;
        stateKey = state: graph.regex.stateKey state;
      }
    );

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

  # `exprOf site at alphabet expression` — the parsed admission expression, under the
  # constructor's own law. The constructor and every reader run THIS, never an `expr` an element
  # carries (den-hoag-dcvpi), so a forged `expr` is inert. O(|expression|), a constant in the data.
  exprOf =
    site: at: alphabet: expression:
    let
      expr = graph.regex.parse expression;
      foreign = filter (l: !(elem l alphabet.letters)) (literalsOf expr);
    in
    if !(builtins.isString expression) then
      refuse site "field '${at}expression' is ${renderValue expression}; it must be a path expression over the alphabet, written as a string"
    else if foreign != [ ] then
      refuse site "${
        if at == "" then "the expression" else "field '${at}expression'"
      } names '${head (sort builtins.lessThan foreign)}', which is not a letter of the alphabet (${quote alphabet.letters}); a path expression ranges over L and a name outside it would match nothing and say nothing"
    else
      expr;

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
  # ── THE LIFT IS Fig. 1's VISIBILITY ORDER, RULE BY RULE, AND IT IS *NOT* LEXICOGRAPHIC OVER THE
  # RANK WORD. ────────────────────────────────────────────────────────────────────────────────
  # Fig. 1, printed 114:5, *Visibility Order* — four rules, transcribed:
  #
  #     <l ⊢ p1 <p p2                 $ <l l                 l <l $              l1 <l l2
  #   ────────────────────      ──────────────────      ──────────────────   ─────────────────────
  #   <l ⊢ s·l·p1 <p s·l·p2     <l ⊢ s <p s·l·p         <l ⊢ s·l·p <p s      <l ⊢ s·l1·p1 <p s·l2·p2
  #
  # Read off the rules: the congruence needs the labels EQUAL, and the fourth rule needs the two
  # DIFFERING labels to be `<l`-COMPARABLE. Nothing licenses ordering two distinct labels that `<l`
  # leaves incomparable — and the paper says so in prose at printed 114:6: *"The prefix order only
  # orders paths that have a common prefix."*
  #
  # ★★★ SO EQUAL RANKS MAY NOT LICENSE CONTINUED RECURSION. A lift that recurses past a position
  # where the labels DIFFER but their ranks are equal is treating incomparability as "comparable so
  # far", and it is strictly FINER than `<p`: it shadows contributions the calculus keeps visible,
  # and the loss lands in the materialized answer. Recursion is licensed by label EQUALITY and by
  # nothing else; where the labels differ, this is the last position that will ever be read.
  #
  # ★ THE EXHAUSTION CASES ARE THE SAME RULE. `$` is a label of L̂ distinct from every letter, so a
  # path that stops is compared against a path that continues by asking whether `$ <l l` — which is
  # a rank comparison between two DISTINCT labels, exactly like the fourth rule. A low `endOfPath`
  # makes stopping outrank everything, so a proper prefix beats its own extensions; a higher one
  # lets continuation on lower-ranked labels beat stopping; and an `endOfPath` EQUAL to some
  # letter's rank leaves stopping and continuing on that letter INCOMPARABLE, which is a sayable
  # and meaningful declaration rather than an accident.
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
      foreign = filter (l: !(elem l alphabet.letters)) flat;
      ranks = foldl' (
        acc: i:
        acc
        // builtins.listToAttrs (
          map (l: {
            name = attrKey l;
            value = i;
          }) (builtins.elemAt layers i)
        )
      ) { } (builtins.genList (i: i) (length layers));
      # Every rank read goes through here, so a label outside L̂ is refused by name at every
      # published reader: `ranks.${l}` aborts past `tryEval` on an unranked name and on a
      # non-string. `ranks`' keys are exactly the alphabet (`missing` and `foreign` below).
      rankOf =
        l:
        let
          k = attrKey l;
        in
        if l == "$" then
          a.endOfPath
        else if builtins.isString l && ranks ? ${k} then
          ranks.${k}
        else
          refuse "labelOrder" "${renderSubject l} is not a label of L̂ (${quote alphabet.letters}, or `$`)";
    in
    if !(builtins.isList layers) || any (l: !(builtins.isList l)) layers then
      refuse "labelOrder" "layers must be a list of lists — each inner list is one rank, and two letters sharing a rank are incomparable, which is how a strict PARTIAL order is declared"
    else if !(builtins.isInt a.endOfPath) then
      refuse "labelOrder" "endOfPath must be an int; it is the rank of the extended label `$` and decides whether stopping outranks continuing"
    else if foreign != [ ] then
      refuse "labelOrder" "layers rank '${head (sort builtins.lessThan foreign)}', which is not a letter of the alphabet (${quote alphabet.letters})"
    else if missing != [ ] then
      refuse "labelOrder" "letter ${renderSubject (head (sortNames missing))} is not ranked; the label order is total over the alphabet, and an unranked letter would otherwise take a default rank nobody declared"
    else
      {
        __element = "labelOrder";
        inherit alphabet layers rankOf;
        inherit (a) endOfPath;
        # `<l` itself: the strict partial order over L̂ the figure defines. Two DISTINCT letters of
        # one layer are incomparable — `precedes` is false in BOTH directions — and a letter is
        # never `<l` itself. Same label ⇒ same rank, so the rank comparison already says this.
        # A label outside L̂ is refused by name in `rankOf`.
        precedes = x: y: rankOf x < rankOf y;

        # ★ A PROJECTION FOR DIAGNOSTICS AND LAYERING, AND EXPLICITLY *NOT* THE BASIS OF THE
        # COMPARISON. It is published because the ranks of a path's labels are worth reading; it is
        # flagged because a reader who assumes `pathPrecedes` is `rankWord` compared
        # lexicographically has the finer, wrong order in mind — which is exactly the defect this
        # element was corrected for.
        rankWord = path: map (step: rankOf step.label) path;

        # Fig. 1's Visibility Order. Recursion is licensed by label EQUALITY; where the labels
        # differ this is the last position read, and the two paths are ordered only if `<l` orders
        # those two labels.
        pathPrecedes =
          pa: pb:
          let
            la = length pa;
            lb = length pb;
            labelAt = p: i: (builtins.elemAt p i).label;
            go =
              i:
              if i >= la && i >= lb then
                false # the same path: `<p` is strict
              else if i >= la then
                rankOf "$" < rankOf (labelAt pb i) # `$ <l l` ⇒ s <p s·l·p
              else if i >= lb then
                rankOf (labelAt pa i) < rankOf "$" # `l <l $` ⇒ s·l·p <p s
              else if labelAt pa i == labelAt pb i then
                go (i + 1) # the congruence, and the ONLY licence to recurse
              else
                # `l1 <l l2` ⇒ ordered; equal ranks on distinct labels ⇒ INCOMPARABLE, false both
                # ways, and the walk stops here rather than reading a position the calculus never
                # reaches.
                rankOf (labelAt pa i) < rankOf (labelAt pb i);
          in
          go 0;

        # ★★ A TOTAL ORDER ON RANK WORDS, PUBLISHED UNDER A NAME THAT SAYS WHAT IT IS: A SORT KEY.
        # It is NOT the visibility order and must never be substituted for one — it is the finer
        # order `pathPrecedes` was corrected away from. `<p` refines it — `a <p b` implies
        # `rankLess a b`, because the first position where the rank words differ can only be a
        # position where the LABELS differ (equal labels have equal ranks), and `<p` decides exactly
        # there — so sorting by it puts every dominator ahead of everything it dominates. Step 6 no
        # longer sorts: it decides minimality as a prefix minimum over LABEL words, and nothing in
        # this library consumes this key; it stays published as the rank-word calculus's total order.
        rankLess =
          pa: pb:
          let
            w = p: map (step: rankOf step.label) p;
          in
          graph.wordLess a.endOfPath (w pa) (w pb);
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
  inherit (import ./elements.nix { inherit prelude; }) elementOf;

  # ── THE CARRIER — the five elements assembled, plus the third label population, and the
  # cross-checks no element can make alone ────────────────────────────────────────────────────
  # Each element validates itself; only the assembly can see whether they are about the same
  # alphabet and whether the three label populations overlap.
  #
  # ★★ `relatumLabels` IS A REQUIRED FIELD AND IS STILL NOT A CARRIER ELEMENT. It is carried here
  # because THIS is the only construction that can see all three populations at once, which is
  # where a pairwise-disjointness law has to be enforced. `carrierElements` stays FIVE: `Λ` indexes
  # nothing in the carrier, and a caller reading the enumeration must not conclude otherwise.
  # Required rather than optional because absence is a decision — a graph with no reified bindings
  # says so by declaring `relatumLabels { names = [ ]; }`.
  carrier =
    args:
    let
      a = fields "carrier" [
        "labels"
        "labelWellFormedness"
        "labelOrder"
        "dataOrder"
        "relations"
        "relatumLabels"
      ] args;
      labels = elementOf "carrier" "labels" "edgeLabels" a.labels;
      wfl = elementOf "carrier" "labelWellFormedness" "labelWellFormedness" a.labelWellFormedness;
      ord = elementOf "carrier" "labelOrder" "labelOrder" a.labelOrder;
      key = elementOf "carrier" "dataOrder" "dataOrder" a.dataOrder;
      rels = elementOf "carrier" "relations" "relations" a.relations;
      roles = elementOf "carrier" "relatumLabels" "relatumLabels" a.relatumLabels;
      # ★ THE THREE-WAY DISJOINTNESS, ALL THREE PAIRS, EACH REFUSED BY NAME.
      # `L ∩ R = ∅` — a name in both would let an admission expression name content, which is the
      #               arrangement the scoped-relations split exists to remove.
      # `L ∩ Λ = ∅` — a role label that is also a letter would make a binding's incidence edge
      #               WALKABLE: the derivative would not go to the empty state, the walk would step
      #               onto a relatum edge, and the inertness argument would be false while still
      #               being written down. This is the collision the law names.
      # `R ∩ Λ = ∅` — a role that is also a relation name makes the classification of an edge
      #               ambiguous, and the partition realisation of the same law is then not a
      #               function.
      lr = filter (r: elem r labels.letters) rels.names;
      llam = filter (l: elem l labels.letters) roles.names;
      rlam = filter (l: elem l rels.names) roles.names;
    in
    if wfl.alphabet.letters != labels.letters then
      refuse "carrier" "labelWellFormedness is built over a different alphabet than `labels` (${quote wfl.alphabet.letters} vs ${quote labels.letters}); one carrier has one L"
    else if ord.alphabet.letters != labels.letters then
      refuse "carrier" "labelOrder is built over a different alphabet than `labels` (${quote ord.alphabet.letters} vs ${quote labels.letters}); one carrier has one L"
    else if lr != [ ] then
      refuse "carrier" "${renderSubject (head (sortNames lr))} is both a letter of L and a name in R; the sorts are disjoint, because the walk steps only on structural letters and a content name reached at the path's end can never enter the label word"
    else if llam != [ ] then
      refuse "carrier" "${renderSubject (head (sortNames llam))} is both a letter of L and a relatum label in Λ; the populations are disjoint, because a role label that is also a letter would make a binding's incident edge WALKABLE and the inertness that keeps a binding out of the traversal would be false"
    else if rlam != [ ] then
      refuse "carrier" "${renderSubject (head (sortNames rlam))} is both a name in R and a relatum label in Λ; the populations are disjoint, because an edge carrying it could not be classified into one of them"
    else
      decided [ key ] {
        __element = "carrier";
        inherit labels;
        relations = rels;
        relatumLabels = roles;
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
  # ★★★ `data` IS A PLAIN COMPONENT OF THE GRAPH VALUE — A SET OF DATUMS, NOT AN ACCESSOR AND NOT A
  # FUNCTION OF ANYTHING. Fig. 1 writes it that way and the reason is the whole of this design:
  # `data(G)` is a COMPONENT, so a datum is in it or it is not, and NO TRAVERSAL CAN PUT ONE THERE.
  # (NR-Rel) reads `s′ —r→ d ∈ data(G)` — a membership test against a value that existed before any
  # walk began.
  #
  # ★★★ AN EARLIER REVISION MADE `data` A FUNCTION OF THE GRAPH, AND THAT DIVERGENCE IS WITHDRAWN.
  # Owner-ruled: taking the graph as a parameter is precisely what made WALK-DEPENDENCE SAYABLE —
  # an accessor could consult the graph and re-emit, at one scope, datums it found by walking out
  # of it. Having opened that hole, the library then invented a discriminator to detect what had
  # fallen through it, and the discriminator was incomplete (it severed one scope's out-edges, so
  # any walk-dependence routed through other edges survived, and at a SINK scope severing was the
  # identity and the check was vacuous). ⇒ SUBSTRATE RE-EMISSION IS NOW INEXPRESSIBLE RATHER THAN
  # DETECTED, and the claim is SCOPED TO WHAT THE SHAPE EARNS: no traversal can change WHICH datums
  # are in the component or WHERE they are filed. A datum's VALUE is the author's and is not
  # analysed — a caller may compute one from the graph, and doing so IS authoring it.
  # BY-CONSTRUCTION OVER REPAIR, applied to the construction that opened the hazard rather than to
  # the mechanism that chased it. There is no discriminator here because there is nothing to
  # discriminate.
  #
  # ★★ AND R17's SHAPE REQUIREMENT IS SATISFIED BY THE COMPONENT SHAPE, not by a declaration field
  # and not by a check. What competes is exactly what is IN the data component, and the only way a
  # value gets there is for an author to write it there — so AUTHORING INTO THE COMPONENT *IS* THE
  # DECLARATION. A walk answer has no route in: `datum` entries are closed to `{ scope; relation;
  # datum; }`, so a contribution — which carries `path`, `admission`, `distance` and `channel` —
  # is refused BY NAME in a data position, and stripping it back to the three fields is an act of
  # authorship performed by a person.
  #
  # ★★★ EVERY EDGE LABEL IS CHECKED FOR EXHAUSTIVENESS OVER THE *THREE* POPULATIONS, NOT FOR
  # MEMBERSHIP IN `L`. The law is `labels(edges(G)) ⊆ L ⊎ R ⊎ Λ` — disjoint AND jointly exhaustive,
  # refused at construction — and the disjointness half is `carrier`'s. A guard demanding
  # membership in `L` alone is that law INVERTED: it refuses the one case the law requires to be
  # present (a non-colliding relatum edge, held and inert) and accepts the one case the law
  # requires to be refused (a role label colliding with a letter, which would make a binding's
  # incidence WALKABLE). It would also make this library unable to hold a graph containing any
  # reified binding at all, which is every graph the minter produces.
  #
  # ★ WHAT `Λ` AND `R` EDGES ARE: HELD AND NOT WALKED. Their inertness needs no check here because
  # it is structural — `labelWellFormedness` admits no literal outside `L`, and the three
  # populations are disjoint, so the Brzozowski derivative with respect to such a label is the
  # empty state and the walk prunes at that edge. Present in the edge set, invisible to WFL, read
  # as datums by nothing.
  #
  # ★ `R` IS ADMITTED HERE THOUGH THIS LIBRARY TAKES THE OTHER REALISATION. The law offers two: a
  # PARTITION of one accessor by population, or a SEPARATE data component beside it. gen-view takes
  # the separate component — `data` below — so its datums do not ride on `labeledEdges`. Admitting
  # an `R` label anyway is the stated condition read literally, and such an edge is inert by the
  # same argument; refusing it would be narrowing a law this library does not own.
  # `labeledOf site at c scopes edges` — the labeled graph of a scopeGraph, derived from its checked
  # structure. The constructor and every reader run THIS, never a `labeled` an element carries
  # (den-hoag-cer8j), so a forged `labeled` is inert and forged `edges`/`scopes` meet the
  # constructor's own law, refused at the reading door. An accessor's RESULT is the graph's law
  # wherever it is applied, so its refusal names `scopeGraph` at every door. A read costs
  # O(|scopes|) for `strings` and the scope index, plus O(|edge labels|·(|L|+|R|+|Λ|)) for
  # `unclassified`, a constant in the data.
  labeledOf =
    site: at: c: scopes0: edges:
    let
      fieldName = n: if at == "" then n else "field '${at}${n}'";
      scopes = strings site (fieldName "scopes") scopes0;
      scopeIndex = genAttrs (map builtins.unsafeDiscardStringContext scopes) (_: null);
      edgeLabelNames = builtins.attrNames edges;
      unclassified = filter (
        l: !(elem l c.labels.letters || elem l c.relations.names || elem l c.relatumLabels.names)
      ) edgeLabelNames;
      patterned = sortNames (filter (l: formalsOf edges.${l} != [ ]) edgeLabelNames);
      nonAccessor = sort builtins.lessThan (filter (l: !(builtins.isFunction edges.${l})) edgeLabelNames);
      labeled = graph.labeledFrom {
        perLabel = builtins.mapAttrs (
          l: acc: s:
          let
            out =
              returned "scopeGraph" "the edge accessor ${renderSubject l} at scope ${renderSubject s}"
                "each label's value is the accessor scope → [ scope ]"
                builtins.isList
                (acc s);
          in
          if !(elem l c.labels.letters) then
            out
          else
            map (
              t:
              if builtins.isString t && scopeIndex ? ${builtins.unsafeDiscardStringContext t} then
                t
              else
                refuse "scopeGraph" "the edge accessor ${renderSubject l} at scope ${renderSubject s} returned the target ${renderValue t}, which is not a scope of this graph (${quote scopes}); an L edge is `s —l→ s′` between scopes of the graph"
            ) out
        ) edges;
        nodes = scopes;
      };
    in
    if !(builtins.isAttrs edges) then
      refuse site "${fieldName "edges"} must be an attrset of label → (scope → [ scope ]); it is the per-label accessor the walk steps"
    else if unclassified != [ ] then
      refuse site "${fieldName "edges"} carry the label '${head (sort builtins.lessThan unclassified)}', which is in none of the three populations — L (${quote c.labels.letters}), R (${quote c.relations.names}) or Λ (${quote c.relatumLabels.names}); the classification of an edge label is total, and a label outside all three would be walked by nothing and classified as nothing"
    else if patterned != [ ] then
      refuse site "the edge accessor ${renderSubject (head patterned)} destructures an attrset (formals: ${
        quote (formalsOf edges.${head patterned})
      }); it is applied to a scope id, a string, so it can never be applied"
    else if nonAccessor != [ ] then
      refuse site "${fieldName "edges"} carry the label '${head nonAccessor}' bound to ${
        renderValue edges.${head nonAccessor}
      }; each label's value must be the accessor scope → [ scope ] the walk steps"
    else
      builtins.seq (builtins.length scopes) labeled;

  # `dataLaw site at c scopes data` — the data component under the constructor's own law, returned
  # unchanged. The constructor and every reader run THIS and index what it returns (`indexData`),
  # never a `datumsAt` an element carries (den-hoag-dcvpi), so a forged `datumsAt` is inert and a
  # forged `data` meets the constructor's refusals at the reading door. `scopes` must already be
  # checked (`strings`). O(|data|) plus O(|scopes|) for the scope index.
  dataLaw =
    site: at: c: scopes: data:
    let
      fieldName = n: if at == "" then n else "field '${at}${n}'";
      aDatum = if at == "" then "a datum" else "a datum of field '${at}data'";
      # `Data ::= s —r→ d` — THREE components and no more. The field set is CLOSED, and that is
      # what makes a walk answer unsayable here: a contribution carries `path`, `admission`,
      # `distance` and `channel` besides, so it is refused in a data position BY NAME rather than
      # silently accepted and carried into competition.
      datumFields = [
        "scope"
        "relation"
        "datum"
      ];
      malformed = filter (
        e:
        !(builtins.isAttrs e)
        || sort builtins.lessThan (builtins.attrNames e) != sort builtins.lessThan datumFields
      ) (if builtins.isList data then data else [ ]);
      scopeIndex = genAttrs (map builtins.unsafeDiscardStringContext scopes) (_: null);
      offScope = filter (
        e: !(builtins.isString e.scope && scopeIndex ? ${builtins.unsafeDiscardStringContext e.scope})
      ) (if builtins.isList data then data else [ ]);
      offRelation = filter (e: !(elem e.relation c.relations.names)) (
        if builtins.isList data then data else [ ]
      );
    in
    if builtins.isFunction data then
      refuse site "${fieldName "data"} is a FUNCTION; it must be a plain list of datums `[ { scope; relation; datum; } ]`. In the calculus `data(G)` is a COMPONENT of the graph, so a datum is in it or it is not and no traversal can put one there — a function is what let the substrate's own accessor re-emit, which is the one shape the component form exists to remove"
    else if !(builtins.isList data) then
      refuse site "${fieldName "data"} must be a list of datums `[ { scope; relation; datum; } ]` — Fig. 1's `Data ::= s —r→ d`, the ⟨scopes, edges, data⟩ triple's third component"
    else if malformed != [ ] then
      refuse site "${aDatum} carries the fields (${quote (builtins.attrNames (head malformed))}); a datum is exactly `{ scope; relation; datum; }` and the field set is closed. A WALK ANSWER CANNOT BE A DATUM: a contribution carries its path, its residual admission state and its distance, none of which a component of the graph can hold — strip it to the three fields and you have authored one"
    else if offScope != [ ] then
      refuse site "${aDatum} is filed at scope ${renderSubject (head offScope).scope}, which is not a scope of this graph (${quote scopes})"
    else if offRelation != [ ] then
      refuse site "${aDatum} is filed under relation ${renderSubject (head offRelation).relation}, which is not a name in R (${quote c.relations.names}); the sort a datum is reached by is declared, and an undeclared one is reachable by no query"
    else
      data;

  # `indexData data` — the per-scope index of a CHECKED data component (`dataLaw`'s result), DERIVED
  # and never a second source: `data` remains the component the figure names, and this is how it is
  # read.
  #
  # `ordinal` is the entry's position in `data` AS AUTHORED — indexed here, at the component, never
  # in a materialization: an author's own declaration is one coordinate regardless of how many paths
  # later reach it. It is stamped over data `dataLaw` has already checked, so an authored `ordinal`
  # field is refused by name (the closed set is the three) before this index is ever built.
  indexData = data: builtins.groupBy (e: attrKey e.scope) (imap0 (i: e: e // { ordinal = i; }) data);

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
      # The scopes `labeledOf` checked, so `strings` runs once per construction.
      scopes = labeled.nodes;
      # Each accessor's RESULT is checked where the walk consumes it: a list, on every label. The
      # TARGET is checked only on an L label, where `Edges ::= s —l→ s` makes it a scope of this
      # graph; an R edge's target is a datum (`s —r→ d`) and a Λ edge's is a binding node, both
      # admitted above as inert, so narrowing their targets would narrow a law this library does not
      # own. A target is forced to WHNF only when the walk reads it, as it would be unchecked.
      labeled = labeledOf "scopeGraph" "" c a.scopes a.edges;
      data = dataLaw "scopeGraph" "" c scopes a.data;
      datumsAt = indexData data;
    in
    builtins.seq data (
      builtins.seq labeled decided [ c scopes ] {
        __element = "scopeGraph";
        carrier = c;
        inherit scopes labeled datumsAt;
        inherit (a) edges data;
      }
    );

  # `entriesOf g` — (NR-Rel) over ONE graph, restated from its checked structure: the index is built
  # once per `entriesOf g` and every scope reads it. `relationEntries` is this at one scope, and
  # `viewRelation` binds it once per relation, so both run the one definition and its refusals and
  # a materialization pays the data law once, not once per reached scope.
  entriesOf =
    g:
    let
      datumsAt = indexData (
        dataLaw "relationEntries" "graph." g.carrier (strings "relationEntries" "field 'graph.scopes'"
          g.scopes
        ) g.data
      );
    in
    a:
    if !(elem a.relation g.carrier.relations.names) then
      refuse "relationEntries" "${renderSubject a.relation} is not a name in R (${quote g.carrier.relations.names}); an undeclared relation is refused rather than answered empty, because an empty answer cannot be told from a relation with no datums"
    else if !(builtins.isFunction a.wellFormed) then
      refuse "relationEntries" "wellFormed must be a predicate on data terms; it is WFD, the visibility parameter that decides whether the datum found at the path's end is the one being looked for"
    # `datumsAt.${scope}` aborts past `tryEval` on a non-string, so the type is refused by name.
    else if !(builtins.isString a.scope) then
      refuse "relationEntries" "scope is ${renderValue a.scope}; a scope is named by a string"
    else
      filter (
        entry:
        entry.relation == a.relation
        &&
          returned "relationEntries"
            "wellFormed (WFD), for the datum at scope ${renderSubject a.scope} under relation ${renderSubject a.relation},"
            "it is a predicate on data terms and must return a bool"
            builtins.isBool
            (a.wellFormed entry.datum)
      ) (datumsAt.${attrKey a.scope} or [ ]);

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
  # ★★ IT READS THE COMPONENT AND TAKES NO GRAPH-TO-READ-IT-AGAINST, because there is only one
  # reading. The earlier signature carried a `labeled` argument so a caller could pass a modified
  # graph and get a different answer at the same scope — which is the walk-dependence the component
  # shape removes. A membership test against a value has no such parameter, and its absence is what
  # makes the rule total.
  #
  # ★ COST: each call restates the graph's index from `data` (`entriesOf g`), O(|scopes| + |data|)
  # PER CALL, because a forged `datumsAt` is a claim and a memo stored in the element would be one
  # too. One call per scope over one graph is therefore quadratic — one datum per scope at 1,000
  # scopes, 498,611 → 12,513,625 calls (den-hoag-dcvpi). `viewRelation` binds `entriesOf g` once
  # per relation and does not pay this.
  relationEntries =
    args:
    let
      a = fields "relationEntries" [
        "graph"
        "scope"
        "relation"
        "wellFormed"
      ] args;
    in
    entriesOf (elementOf "relationEntries" "graph" "scopeGraph" a.graph) a;

  # `relationLookup` — the datum projection over `relationEntries`. It carries no refusal of its
  # own: every site above belongs to `relationEntries`, the component reading, and this is
  # `map (entry: entry.datum)` composed onto it — unchanged in shape and behavior from the single
  # layer it replaces, for the callers that want the datum and not its authored coordinate.
  relationLookup = args: map (entry: entry.datum) (relationEntries args);
in
{
  inherit
    edgeLabels
    relations
    relatumLabels
    labelWellFormedness
    labelOrder
    dataOrder
    carrier
    scopeGraph
    labeledOf
    exprOf
    entriesOf
    relationLookup
    relationEntries
    elementOf
    ;
}
