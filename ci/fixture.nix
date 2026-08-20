# THE SHARED FIXTURE — one carrier, one scope graph, one declaration, reached by every suite.
#
# It lives OUTSIDE `./tests` deliberately: `testModules` is the whole of `flake.tests`, so a plain
# value module in that tree would be read as a suite and contribute cells of its own. This is a
# function of the library under test and nothing else, so every suite builds its fixtures from the
# same construction rather than from a private near-copy that can drift out of step with it.
#
# ★ THE ALPHABET AND THE RELATION SORT ARE DEN'S OWN INSTANCE, ON PURPOSE. Under the
# scoped-relations arrangement `import`, `expose-in`, `broadcast-in` and `policy` are RELATIONS,
# not letters — they were an admission alphabet made entirely of binding-kinds sitting in a
# substrate position with NO STRUCTURAL LETTER, which is what forced one content symbol to double
# as the ancestor relay. Here the structural letters are `parent` and `include`, the four kinds are
# names in R, and `include` is expressible as a letter without a fifth structural symbol being
# added to carry containment. If this fixture could not be built, the ruling would have been
# recorded and not built.
{ genView }:
let
  v = genView;

  labels = v.edgeLabels {
    letters = [
      "parent"
      "include"
    ];
  };

  relations = v.relations {
    names = [
      "import"
      "expose-in"
      "broadcast-in"
      "policy"
    ];
  };

  admission = v.labelWellFormedness {
    alphabet = labels;
    expression = "(parent|include)*";
  };

  # A NON-EMPTY label order: `include` outranks `parent`, so a containment reach shadows an
  # ancestor reach at the same competition key. This is the carrier instance no shipped
  # composition supplies.
  order = v.labelOrder {
    alphabet = labels;
    layers = [
      [ "include" ]
      [ "parent" ]
    ];
    endOfPath = -1;
  };

  # The FLAT order — one layer holding every letter, so no letter outranks another. The contrast
  # between the two is what shows the order is read rather than decorative.
  flatOrder = v.labelOrder {
    alphabet = labels;
    layers = [
      [
        "include"
        "parent"
      ]
    ];
    endOfPath = -1;
  };

  key = v.dataOrder {
    channel = "settings";
    keyOf = _: "settings";
  };

  # The VACUOUS key — one group per scope, which is the shipped per-node default this carrier
  # refuses to have. Kept here as the mutant O3 and the discipline suite compare against.
  perScopeKey = v.dataOrder {
    channel = "settings";
    keyOf = c: c.scope;
  };

  # Λ — the relatum-role labels. DECLARED here and carried by every graph below; the main fixture
  # graph deliberately holds NO Λ edge, so it stays the L-only regression subject while the role
  # graph in `ci/tests/carrier.nix` exercises the population.
  roles = v.relatumLabels {
    names = [
      "relatum-target"
      "relatum-source"
    ];
  };

  carrier = v.carrier {
    inherit labels relations;
    relatumLabels = roles;
    labelWellFormedness = admission;
    labelOrder = order;
    dataOrder = key;
  };

  scopes = [
    "root"
    "mid"
    "leaf"
    "inc"
  ];

  edges = {
    parent =
      id:
      {
        leaf = [ "mid" ];
        mid = [ "root" ];
      }
      .${id} or [ ];
    include = id: if id == "leaf" then [ "inc" ] else [ ];
  };

  # `authored { <scope> = [ { relation; datum; } ]; }` — the data COMPONENT, flattened to Fig. 1's
  # own shape `Data ::= s —r→ d`. It is a plain value: no function, nothing to consult, nothing a
  # traversal could reach into. The per-scope attrset is the ergonomic form a fixture wants to
  # write; the triples are what the graph holds.
  authored =
    entries:
    builtins.concatMap (
      scope:
      map (e: {
        inherit scope;
        inherit (e) relation datum;
      }) entries.${scope}
    ) (builtins.attrNames entries);

  datums = {
    root = [
      {
        relation = "import";
        datum = [ "root" ];
      }
    ];
    mid = [
      {
        relation = "import";
        datum = [ "mid" ];
      }
    ];
    inc = [
      {
        relation = "import";
        datum = [ "inc" ];
      }
      {
        relation = "policy";
        datum = [ "not-this-relation" ];
      }
    ];
  };

  graph = v.scopeGraph {
    inherit carrier scopes edges;
    data = authored datums;
  };

  # The same graph with a DUPLICATE datum, so the dedup policy has something to drop and the
  # drop record has something to be about.
  dupGraph = v.scopeGraph {
    inherit carrier scopes edges;
    data = authored (
      datums
      // {
        root = [
          {
            relation = "import";
            datum = [ "mid" ];
          }
        ];
      }
    );
  };

  # WFD, hoisted to ONE binding rather than written inline at each call site. Two structurally
  # identical Nix lambdas are NOT equal, so a fixture that wrote this predicate twice would make
  # two declarations differing in nothing compare unequal — and any "these differ in exactly one
  # respect" control over them would then be measuring the language rather than the fixtures.
  admitAll = _: true;

  # `mkDefinition` — the fixture declaration, with every field overridable by name so a suite can
  # alter EXACTLY ONE respect and nothing else. That is what makes the O3 mutants honest: a mutant
  # that differed in two places could pass its own rejection for the wrong reason.
  mkDefinition =
    overrides:
    v.compositions.movement (
      {
        channel = "settings";
        relation = "import";
        root = "leaf";
        direction = "outbound";
        inherit admission order;
        wellFormed = admitAll;
        tieSet = v.tieSets.union;
        empty = [ ];
        combine = v.combines.listAppend;
        dedup = v.dedups.none;
      }
      // overrides
    );

  definition = mkDefinition { };

  # The RAW declaration's complete argument set — the substrate's own twelve fields, not the
  # composition's eleven. The refusal sweep removes one at a time from this, so "each omitted field
  # refuses by name" quantifies over the library's own published field enumeration rather than over
  # a list somebody typed twice.
  definitionArgs = {
    channel = key;
    relation = "import";
    root = "leaf";
    direction = "outbound";
    inherit admission order;
    wellFormed = admitAll;
    distance = s: s.distance + 1;
    tieSet = v.tieSets.union;
    empty = [ ];
    combine = v.combines.listAppend;
    dedup = v.dedups.none;
  };

  noMarks = _: [ ];

  # A boundary mark on `leaf` refusing the containment letter. `boundedBy`'s contract: a mark is
  # `{ name; admits; }` — a NAME the diagnostic can quote and a `label → bool` predicate.
  includeMark =
    id:
    if id == "leaf" then
      [
        {
          name = "no-containment";
          admits = l: l != "include";
        }
      ]
    else
      [ ];

  # A mark that admits EVERYTHING. It is the widening probe: the strongest mark a caller can write
  # still cannot add an edge, because the construction only ever removes them.
  admitAllMark = _: [
    {
      name = "admits-everything";
      admits = _: true;
    }
  ];

  mkRelation =
    args:
    v.viewRelation (
      {
        inherit definition graph;
        marks = noMarks;
      }
      // args
    );

  relation = mkRelation { };

  placement = v.placement.place {
    mode = "merge";
    path = [ "settings" ];
    name = "settings";
    value = relation.value;
  };
in
{
  inherit
    v
    labels
    relations
    admission
    order
    roles
    flatOrder
    key
    perScopeKey
    carrier
    scopes
    edges
    datums
    authored
    graph
    dupGraph
    admitAll
    mkDefinition
    definition
    definitionArgs
    noMarks
    includeMark
    admitAllMark
    mkRelation
    relation
    placement
    ;
}
