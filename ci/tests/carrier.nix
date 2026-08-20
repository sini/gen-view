# ORACLE O4 — THE RAW CALCULUS IS PUBLISHED, NOT ONLY THE COMPOSITIONS.
#
# Two claims, and the second is the one that can rot silently:
#   (i)  each of the five carrier elements is reachable as a NAMED EXPORT, and a caller can build
#        a view over a carrier instance NO SHIPPED COMPOSITION SUPPLIES;
#   (ii) the movement composition constructs over THOSE SAME EXPORTS — so the raw layer is the one
#        the composition uses and not a parallel surface kept beside it for show.
#
# ★ (ii) IS THE CONTROL AND IT IS NOT DECORATION. A library can publish five constructors, build
# its compositions from five private twins, and satisfy (i) forever while the published layer
# drifts out of step with the one that runs. The check is a VALUE identity: the element the caller
# built is the element the declaration holds.
#
# ★★ AND THE OTHER FAILURE O4 NAMES IS THE ONE THAT SAYS WHETHER A RULING WAS BUILT OR ONLY
# RECORDED: den's four binding kinds must be EXPRESSIBLE OVER THE PUBLISHED CARRIER as RELATIONS,
# with `include` available as a structural letter and no fifth structural symbol added to carry
# containment.
{ genView, ... }:
let
  f = import ../fixture.nix { inherit genView; };
  v = genView;

  # The layered order and the flat order differ in exactly one respect. Everything else about the
  # two declarations is the same construction.
  layered = f.relation;
  flat = f.mkRelation { definition = f.mkDefinition { order = f.flatOrder; }; };
  scopesOf = r: map (c: c.scope) r.contributions;
in
{
  flake.tests.carrier = {
    # ── (i) THE FIVE ARE REACHABLE, AND A CALLER BUILDS OVER THEM DIRECTLY ──
    # A carrier assembled from the five published constructors, with no composition involved at
    # any step. If any element were reachable only through a composition this could not be written.
    test-a-carrier-is-assembled-from-the-published-elements-alone = {
      expr = builtins.attrNames f.carrier;
      expected = [
        "__element"
        "dataOrder"
        "labelOrder"
        "labelWellFormedness"
        "labels"
        "relations"
      ];
    };

    # THE CARRIER INSTANCE NO SHIPPED COMPOSITION SUPPLIES: a NON-EMPTY label order, under which
    # the containment letter outranks the ancestor letter. The answer differs from the flat order's
    # answer, which is what shows the order is READ rather than carried.
    test-a-non-empty-label-order-changes-which-contribution-survives = {
      expr = {
        layered = scopesOf layered;
        flat = scopesOf flat;
      };
      expected = {
        layered = [ "inc" ];
        flat = [
          "inc"
          "mid"
        ];
      };
    };

    # ★ THE CONTROL FOR THE CELL ABOVE, IN THE SAME RUN: the two declarations differ in the ORDER
    # ELEMENT AND IN NOTHING ELSE. Without it, two different answers are equally consistent with
    # two fixtures that differ somewhere nobody looked.
    #
    # ★★ THE RAW-LAMBDA FIELDS ARE COMPARED BY NAME AND NOT BY VALUE, AND THAT IS A FACT ABOUT THE
    # LANGUAGE RATHER THAN A WEAKENING. Measured on this evaluator: `==` on two bare function
    # values is FALSE EVEN AGAINST ITSELF — `{ v = d.distance; } == { v = d.distance; }` reads
    # false for one and the same attribute. So `wellFormed`, `distance` and the key's closure are
    # excluded from the structural comparison and checked by the names they are built from; every
    # remaining field, INCLUDING the element attrsets that carry functions inside them, compares by
    # value because both declarations hold the same constructed element.
    test-control-the-two-declarations-differ-only-in-the-order-element = {
      expr = {
        everyInertField =
          removeAttrs layered.definition [
            "order"
            "channel"
            "wellFormed"
            "distance"
          ] == removeAttrs flat.definition [
            "order"
            "channel"
            "wellFormed"
            "distance"
          ];
        sameName = layered.definition.name == flat.definition.name;
        sameFieldSet = builtins.attrNames layered.definition == builtins.attrNames flat.definition;
        orderReallyChanged = layered.definition.order != flat.definition.order;
      };
      expected = {
        everyInertField = true;
        sameName = true;
        sameFieldSet = true;
        orderReallyChanged = true;
      };
    };

    # ── (ii) THE COMPOSITION USES THE PUBLISHED ELEMENTS, NOT PRIVATE TWINS ──
    test-control-the-movement-composition-holds-the-very-elements-the-caller-built = {
      expr = {
        admission = layered.definition.admission == f.admission;
        order = layered.definition.order == f.order;
      };
      expected = {
        admission = true;
        order = true;
      };
    };

    # ★ AND THE IDENTITY CHECK IS SHOWN ABLE TO FAIL. Two structurally equal elements built twice
    # would compare equal in Nix, so the cell above is only meaningful if the comparison can
    # distinguish anything at all — here, an element that is genuinely different.
    test-control-the-element-identity-check-discriminates = {
      expr = layered.definition.order == f.flatOrder;
      expected = false;
    };

    # ── THE RULING IS BUILT, NOT MERELY RECORDED ──
    # den's four binding kinds are RELATIONS in R, `include` is a structural LETTER in L, and the
    # two populations are disjoint. The alphabet carries no fifth structural symbol for containment
    # — the containment letter falls out of the arrangement rather than being added by a separate
    # act.
    test-dens-four-binding-kinds-are-relations-not-letters = {
      expr = {
        relations = f.relations.names;
        letters = f.labels.letters;
        overlap = builtins.filter (r: f.labels.member r) f.relations.names;
      };
      expected = {
        relations = [
          "import"
          "expose-in"
          "broadcast-in"
          "policy"
        ];
        letters = [
          "parent"
          "include"
        ];
        overlap = [ ];
      };
    };

    # And a view over one of those relations MATERIALIZES — the ruling is expressible end to end,
    # not merely declarable. `policy` reaches exactly the one datum filed under it.
    test-a-view-over-a-relation-materializes = {
      expr = (f.mkRelation { definition = f.mkDefinition { relation = "policy"; }; }).value;
      expected = [ "not-this-relation" ];
    };

    # ── (NR-Rel): THE RELATION IS REACHED ONCE, AT THE END OF THE PATH ──
    # The lookup is over the data component and takes WFD; the walk never steps on a relation name.
    test-relation-lookup-is-the-terminus-rule = {
      expr = v.relationLookup {
        graph = f.graph;
        labeled = f.graph.labeled;
        scope = "inc";
        relation = "import";
        wellFormed = _: true;
      };
      expected = [ [ "inc" ] ];
    };

    # WFD narrows the DATUM, never the path — the second premise of (NR-Rel) doing its own work.
    test-control-wfd-narrows-the-datum-and-not-the-path = {
      expr = v.relationLookup {
        graph = f.graph;
        labeled = f.graph.labeled;
        scope = "inc";
        relation = "import";
        wellFormed = d: d != [ "inc" ];
      };
      expected = [ ];
    };

    # ── THE EXTENDED ALPHABET IS DERIVED, NOT DECLARED ──
    # `$` "indicates the end of a path", which is a property of every alphabet rather than a choice
    # about one, so it is never a letter a caller writes.
    test-the-extended-alphabet-is-derived = {
      expr = f.labels.extended;
      expected = [
        "parent"
        "include"
        "$"
      ];
    };

    # ── THE LABEL ORDER IS A STRICT PARTIAL ORDER OVER THE EXTENDED ALPHABET ──
    # Two letters in ONE layer are incomparable in both directions; that is what layers buy over a
    # flat ranking, and it is why "no specificity at all" is expressible rather than accidental.
    test-two-letters-in-one-layer-are-incomparable = {
      expr = {
        forward = f.flatOrder.precedes "include" "parent";
        backward = f.flatOrder.precedes "parent" "include";
        layeredForward = f.order.precedes "include" "parent";
        layeredBackward = f.order.precedes "parent" "include";
      };
      expected = {
        forward = false;
        backward = false;
        layeredForward = true;
        layeredBackward = false;
      };
    };

    # The end-of-path rank ranks `$`, and at the shipped value stopping outranks everything — a
    # proper prefix beats its own extensions.
    test-the-end-of-path-rank-makes-a-prefix-beat-its-extensions = {
      expr =
        f.order.pathPrecedes
          [ { label = "parent"; } ]
          [
            { label = "parent"; }
            { label = "parent"; }
          ];
      expected = true;
    };
  };
}
