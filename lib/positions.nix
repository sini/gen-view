# HEAD POSITIONS — a structural graph lifted to one copy per declared head letter, so a datum's word
# is `h · (structural word)` and the visibility order compares the head letter FIRST.
#
# ★★ WHY THE HEAD AND NEVER THE TAIL. Fig. 1's visibility order decides at the FIRST position where
# two words differ (`pathPrecedes`, `carrier.nix`). A ranked letter at the head of every word is
# therefore compared before any structural letter, and structure decides only between words sharing
# one head. The same letter at the tail is compared only after the structure has already differed,
# so structure decides and the rank is never read: measured on ADR-0029's reconsideration
# (den-hoag-zakjg, cells `rTail_k2`/`rTail_k4`), that placement returns a plausible wrong answer and
# refuses nothing. Nothing in the raw calculus knows a letter is a head, and a raw `viewRelation`
# still accepts a tail-placed rank; the invariant is this construction's, held at its door.
#
# ★★ THE CONSTRUCTION (a product with the head letters):
#   · a fresh root, `[]`, the only scope with a head edge; head `h` steps it to `⟨root, h⟩`
#   · position `⟨s, h⟩` for every structural scope `s` and head `h`, keyed as the JSON of `[s, h]`
#     (injective on pairs of strings, and never `[]`)
#   · a structural edge `s —l→ s′` becomes `⟨s, h⟩ —l→ ⟨s′, h⟩` for every `h`, so a walk never
#     changes its head after the first step
#   · a datum placed at `s` under head `h` is filed at `⟨s, h⟩`
# So every word the walk can produce is one head letter followed by a structural word, BY THE SHAPE
# OF THE EDGE SET: a tail-placed head has no edge to label.
#
# ★★ THE DOOR, WHICH IS WHAT KEEPS THAT TRUE:
#   · `heads` is an ORDERED LIST of distinct strings, one rank per letter. A rank tie between two
#     distinct head letters has no spelling, because a list position holds one letter: it is not a
#     filter over a layered form that could have said it.
#   · a head letter that is also a structural letter is refused by name. A structural edge carrying
#     it would put a ranked letter inside the structural word, which is the tail placement again.
#   · the structure's own data and any edge that is not a structural letter are refused: a datum
#     enters a position only through `data`, under a head letter, never headless.
#   · there is no caller-mark parameter: the order mark is the head ranks, outermost, and one tied
#     structural layer. The landing that adds a caller's mark owes the composed cell and a second
#     refusal (a head letter in the caller's mark layers).
#
# ★ WHAT IT RETURNS IS DATA. `graph` is the product scope graph; `admission` and `order` are its
# carrier's (the head alternation before the structure's own expression; the structure's own query
# order with every head letter in one tied layer ahead of it, which the order mark always decides
# first); `orderMark` ranks each head letter in its own layer in list order, then every structural
# letter with `$` in one layer, so within one head the query order decides; `owners` maps each
# position back to its `{ scope; head; }` and `scopes` is the structure's own, which is what a join
# reads (`joinedTrace`); `position s h` is a position's id, for a caller declaring an order over
# positions (`tieSets.orderedFold`).
{ prelude, graph }:
let
  inherit (prelude)
    map
    filter
    elem
    head
    concatMap
    ;
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude; };
  inherit (import ./elements.nix { inherit prelude; }) elementOf;
  inherit (refusal)
    fields
    refuse
    renderValue
    renderSubject
    strings
    quote
    decided
    attrKey
    ;

  headPositions =
    args:
    let
      site = "headPositions";
      a = fields site [
        # The resolution calculus whose `wellFormed` and `labelOrder` build the lifted E and <
        # (den-hoag-gayc D14). It is the same authority a `viewRelation` over the result is handed.
        "engine"
        "heads"
        "structure"
        "root"
        "data"
      ] args;
      heads =
        if !(builtins.isList a.heads) then
          refuse site "field 'heads' is ${renderValue a.heads}; it must be an ORDERED LIST of head letters, one rank per position"
        else if builtins.any builtins.isList a.heads then
          refuse site "field 'heads' carries a list where a head letter belongs; `heads` is an ORDERED LIST of letters, one rank per position, so two letters sharing a rank cannot be written"
        else if a.heads == [ ] then
          refuse site "field 'heads' is empty; a position is reached only by a head letter, so with none declared no datum could be placed"
        else if builtins.elem "$" a.heads then
          refuse site "field 'heads' names '$', which is the end-of-path label of every alphabet and never a letter"
        else
          strings site "field 'heads'" a.heads;
      sg = elementOf site "structure" "scopeGraph" a.structure;
      c = sg.carrier;
      structural = c.labels.letters;
      clash = filter (h: elem h structural) heads;
      nonLetterEdges = filter (l: !(elem l structural)) (builtins.attrNames sg.edges);

      at =
        s: h:
        builtins.toJSON [
          s
          h
        ];
      root = builtins.toJSON [ ];
      owners = builtins.listToAttrs (
        concatMap (
          s:
          map (h: {
            name = at s h;
            value = {
              scope = s;
              head = h;
            };
          }) heads
        ) sg.scopes
      );
      ownerOf = id: owners.${attrKey id} or null;

      labels = carrierLib.edgeLabels { letters = heads ++ structural; };
      # The head step then the structure's own E, built from the published WFL constructors over the
      # structure's term: the expression may be a string or a term, so it is composed, never spliced.
      admission = a.engine.wellFormed {
        alphabet = labels.letters;
        expression = a.engine.wfl.seq [
          (a.engine.wfl.alt (map a.engine.wfl.lit heads))
          c.labelWellFormedness.term
        ];
      };
      order = a.engine.labelOrder {
        alphabet = labels.letters;
        layers = [ heads ] ++ c.labelOrder.layers;
        endOfPath = c.labelOrder.endOfPath + 1;
      };
      orderMark = a.engine.labelOrder {
        alphabet = labels.letters;
        layers = map (h: [ h ]) heads ++ [ structural ];
        endOfPath = builtins.length heads;
      };

      edges =
        builtins.mapAttrs (
          _: acc: id:
          let
            o = ownerOf id;
          in
          if o == null then [ ] else map (t: at t o.head) (acc o.scope)
        ) sg.edges
        // builtins.listToAttrs (
          map (h: {
            name = h;
            value = id: if id == root then [ (at a.root h) ] else [ ];
          }) heads
        );

      datumFields = [
        "scope"
        "head"
        "relation"
        "datum"
      ];
      place =
        d:
        if
          !(builtins.isAttrs d)
          ||
            builtins.sort builtins.lessThan (builtins.attrNames d)
            != builtins.sort builtins.lessThan datumFields
        then
          refuse site "a datum of field 'data' is ${renderValue d}; a placed datum is exactly `{ scope; head; relation; datum; }`, and its head letter is what files it at a position"
        else if !(elem d.head heads) then
          refuse site "a datum of field 'data' is placed under the head ${renderSubject d.head}, which is not a declared head letter (${quote heads})"
        else if !(builtins.isString d.scope && elem d.scope sg.scopes) then
          refuse site "a datum of field 'data' is placed at scope ${renderSubject d.scope}, which is not a scope of the structure (${quote sg.scopes})"
        else
          {
            scope = at d.scope d.head;
            inherit (d) relation datum;
          };

      checked =
        if
          !(builtins.isAttrs a.engine && a.engine ? wellFormed && a.engine ? labelOrder && a.engine ? wfl)
        then
          refuse site "field 'engine' must be the resolution calculus publishing `wellFormed`, `labelOrder` and `wfl`; the lifted admission and order are built by it, and this construct builds neither of its own"
        else if clash != [ ] then
          refuse site "head letter ${renderSubject (head clash)} is also a letter of the structural alphabet (${quote structural}); a head letter labels only the root's edge to a position, and a structural edge carrying it would place a ranked letter inside the word, where the first differing structural letter decides before it is read"
        else if nonLetterEdges != [ ] then
          refuse site "the structure's edges carry the label ${renderSubject (head nonLetterEdges)}, which is not a structural letter (${quote structural}); a datum enters a position only through field 'data', under a head letter"
        else if sg.data != [ ] then
          refuse site "the structure carries ${toString (builtins.length sg.data)} datum(s) of its own; a datum enters a position only through field 'data', under a head letter, and a headless one would be ranked by nothing"
        else if !(builtins.isString a.root && elem a.root sg.scopes) then
          refuse site "field 'root' is ${renderValue a.root}, which is not a scope of the structure (${quote sg.scopes})"
        else if !(builtins.isList a.data) then
          refuse site "field 'data' must be a list of placed datums `[ { scope; head; relation; datum; } ]`"
        else
          true;

      graph = carrierLib.scopeGraph {
        carrier = carrierLib.carrier {
          inherit labels;
          labelWellFormedness = admission;
          labelOrder = order;
          inherit (c) dataOrder relations relatumLabels;
        };
        scopes = [ root ] ++ builtins.attrNames owners;
        inherit edges;
        data = map place a.data;
      };
    in
    decided [ heads checked labels ] {
      inherit (sg) scopes;
      position = at;
      inherit
        graph
        root
        admission
        order
        orderMark
        owners
        ;
    };
in
{
  inherit headPositions;
}
