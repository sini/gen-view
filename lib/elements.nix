# ELEMENT INTAKE — the one tag test every intake goes through, and what it re-checks.
#
# ★★ AN ELEMENT TAG IS A CLAIM, NOT A PROOF (p79do Q1; den-hoag-8rkc's basis: a value asserting
# the marker "has claimed something about its own origin; that is why intake reads the field TYPES
# as well as the marker"). A hand-built record carrying `__element = "unit"` reaches every consumer
# without passing `unit`, so the tag test alone admits it and the consumer meets an abort, or a
# silent answer, later. `elementOf` therefore re-checks the element's STRUCTURAL fields by type,
# all the way down its nested elements, and refuses by name.
#
# ★ STRUCTURE, NEVER CONTENT. A structural field is one the constructor decides (rymxu's `decided`)
# or derives from its arguments: a name, a closed arm, a function, a nested element. Content is
# the computed answer — a view relation's `value`, `contributions`, `shadowed`, `withheld`,
# `dropped` — and is never forced here: its reader checks what it reads. Each check forces one
# field to WHNF and no further, WITH ONE EXCEPTION: the three label-population lists (`letters`,
# and `names` twice) are checked element by element by their constructor's own law, because the
# library decides membership by reading those lists (den-hoag-l83dk). So the cost is the size of
# the element TREE plus, per label-population element in it, that list's law — O(|L|·w) for L,
# w the longest letter, and O(|R|), O(|Λ|) — a constant in the data.
#
# ★ WHAT THIS DOES NOT CLOSE, named so nobody reads it as closed: a forged field of the right TYPE
# carrying the wrong VALUE (a `datumsAt` indexing other data) is the cooperative-caller residue
# 8rkc names. An operation the library can restate from checked structure is restated and never
# applied — `member` from the lists above, the walk's `step` and `stateKey` from gen-graph's kernel
# (l83dk) — so a forged one is a claim nothing here reads; `scopeGraph.labeled` is not yet restated
# (den-hoag-cer8j). A caller-authored function's RESULT is checked where it is applied
# (den-hoag-0gpyq's class). Other lists' ELEMENTS are checked where they are read (`tupleKey`,
# `attrKey`, `rankOf`).
#
# ★ A KIND WITH NO SHAPE HERE IS TAG-TESTED ONLY, EXACTLY AS BEFORE. `elementOf` is consumed
# outside this library (gen-bind's ci imports `carrier.nix` for its own `peerRelation` element),
# and gen-view itself tags kinds no intake admits (`placement`, `accumulatorRelation`,
# `referenceResolution`, `neededBy`). Refusing an unshaped kind would narrow the domain of a
# published check; its structural fields are the OWNING library's to shape.
#
# ★ A SHAPE IS NEVER STRICTER THAN ITS CONSTRUCTOR. The shapes are a second statement of what each
# constructor decides, so every element a constructor builds, over every declared arm, must pass
# its own shape; the `genuine-parity` cells in `ci/forged-intake.nix` hold the two equal. (A
# non-empty `expression` would refuse `labelWellFormedness`'s lawful empty-word expression `""`.)
#
# COST, MEASURED (`nrFunctionCalls`): an intake pays O(its element tree) plus its label lists'
# laws, constant in the data, and a door re-entered with an already-checked value pays it again
# (l83dk, measured: building one `viewRelation` from its constructors re-runs L's law about 15
# times — 346 calls per letter against 22 for one run — so on the name-only path a 5-letter
# alphabet costs 11,789 → 13,056 calls (+11%) and a 2,000-letter one 64,364 → 681,396, and the
# fixture's walk at 400 scopes moves by under 1%). On the scheduling path, which does not
# materialize, `accumulatorOrder` over n units each over its OWN relation costs 1,290 → 5,846
# calls per unit at n = 400 and 1,326 → 5,881 at n = 4000 (4.4×), linear in n. Reading only `.name`
# of a relation pays `datumsAt`'s `groupBy` once per graph (4,570 → 7,855 at 400 scopes). There is
# no memo: a verdict stored in the element is copied by `//` into a forged `genuine // { f = bad; }`,
# so it would be a claim too.
{ prelude }:
let
  inherit (prelude) elem attrNames;
  refusal = import ./refusal.nix { inherit prelude; };
  enums = import ./enumerations.nix { inherit prelude; };
  placement = import ./placement.nix { inherit prelude; };
  inherit (refusal)
    refuse
    decided
    choice
    renderValue
    strings
    ;

  # ── THE LIST LAWS OF THE THREE LABEL POPULATIONS — one definition, run by each constructor
  # (`edgeLabels`, `relations`, `relatumLabels` in carrier.nix) and by the intake below. ───────────
  # ★★ THE LIBRARY READS THESE LISTS, NEVER THE `member` IT PUBLISHES (den-hoag-l83dk), so the lists
  # are what a forged element's membership is decided by, and the intake must hold them to the SAME
  # law the constructor does or a forged list is admitted where its constructor refuses it. One
  # definition is what makes the intake exactly as strict as the constructor and never stricter —
  # `rootNames` in placement.nix is the same arrangement for a root target's names.
  #
  # A label is a word in gen-graph's parse alphabet. This is not decoration: `regex.stateKey`
  # renders a composite with `* | . ( )`, so a label carrying one of those can collide with a
  # composite's canonical rendering and two dissimilar derivative states can share a seen-key.
  isLabelChar =
    c:
    (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || (c >= "0" && c <= "9") || c == "_" || c == "-";
  isLabelWord =
    s:
    let
      n = builtins.stringLength s;
    in
    n > 0 && builtins.all (i: isLabelChar (builtins.substring i 1 s)) (builtins.genList (i: i) n);

  # `lettersLaw site what xs` — L: distinct non-empty strings, at least one, none reserved, each a
  # label word. Returns `xs`.
  lettersLaw =
    site: what: xs:
    let
      letters = strings site what xs;
      reserved = builtins.filter (l: l == "_" || l == "$") letters;
      malformed = builtins.filter (l: !(isLabelWord l)) letters;
    in
    if letters == [ ] then
      refuse site "${what} is empty; an alphabet with no letters admits no path, so every view over it is empty and nothing says why"
    else if reserved != [ ] then
      refuse site "${what} carries the reserved letter '${builtins.head reserved}' — `_` is the any-label wildcard of the path-expression grammar and `$` is the extended label marking the end of a path (van Antwerpen 2018 Fig. 1); neither can also name an edge"
    else if malformed != [ ] then
      refuse site "${what} carries the letter '${builtins.head malformed}', which is outside the label word alphabet [A-Za-z0-9_-]+; a letter carrying an expression metacharacter can collide with a composite's canonical rendering in the derivative state key"
    else
      letters;

  # `relationNamesLaw site what xs` — R: distinct non-empty strings, at least one.
  relationNamesLaw =
    site: what: xs:
    let
      names = strings site what xs;
    in
    if names == [ ] then
      refuse site "${what} is empty; a carrier with no relation sort can reach no datum, and (NR-Rel) is the only rule by which a view reaches content"
    else
      names;

  # `relatumNamesLaw site what xs` — Λ: distinct non-empty strings; empty is lawful.
  relatumNamesLaw =
    site: what: xs:
    strings site what xs;

  t = what: ok: { inherit what ok; };
  str = t "a non-empty string" (v: builtins.isString v && v != "");
  fn = t "a function" builtins.isFunction;
  list = t "a list" builtins.isList;
  set = t "an attrset" builtins.isAttrs;
  bool = t "a bool" builtins.isBool;
  int = t "an int" builtins.isInt;
  any = t "any value" (_: true);
  nul = t "null" (v: v == null);
  arm = arms: { inherit arms; };
  el = kind: { element = kind; };

  # THE SHAPES — one per element kind, a function of the element so an arm can select the fields
  # its variant carries. An arm that is not declared returns only the arm check, so it is refused
  # before any field it would select is read.
  shapes = {
    edgeLabels = _: {
      letters = list;
      extended = list;
      member = fn;
    };
    relations = _: {
      names = list;
      member = fn;
    };
    relatumLabels = _: {
      names = list;
      member = fn;
    };
    labelWellFormedness = _: {
      alphabet = el "edgeLabels";
      literals = list;
      expr = set;
      # `isString`, as the constructor checks it: `""` is the lawful empty-word expression.
      expression = t "a string" builtins.isString;
      step = fn;
      accepts = fn;
      stateKey = fn;
    };
    labelOrder = _: {
      alphabet = el "edgeLabels";
      layers = list;
      endOfPath = int;
      rankOf = fn;
      precedes = fn;
      rankWord = fn;
      pathPrecedes = fn;
      rankLess = fn;
    };
    dataOrder = _: {
      channel = str;
      keyOf = fn;
    };
    carrier = _: {
      labels = el "edgeLabels";
      relations = el "relations";
      relatumLabels = el "relatumLabels";
      labelWellFormedness = el "labelWellFormedness";
      labelOrder = el "labelOrder";
      dataOrder = el "dataOrder";
    };
    scopeGraph = _: {
      carrier = el "carrier";
      scopes = list;
      labeled = set;
      datumsAt = set;
      edges = set;
      data = list;
    };
    tieSet =
      e:
      if !(elem (e.arm or null) enums.tieSetArms) then
        { arm = arm enums.tieSetArms; }
      else
        {
          arm = any;
          order = if e.arm == "orderedFold" then list else nul;
        };
    combine = e: {
      arm = arm enums.combineArms;
      op = fn;
      unit = any;
      associative = bool;
      setSemilattice = bool;
      acc = t "a bool or null" (v: v == null || builtins.isBool v);
    };
    dedup =
      e:
      if !(elem (e.arm or null) enums.dedupArms) then
        { arm = arm enums.dedupArms; }
      else
        {
          arm = any;
          keyOf = if e.arm == "byKey" then fn else nul;
        };
    viewDefinition = _: {
      admission = el "labelWellFormedness";
      order = el "labelOrder";
      channel = el "dataOrder";
      tieSet = el "tieSet";
      combine = el "combine";
      dedup = el "dedup";
      relation = str;
      root = str;
      direction = arm enums.directions;
      wellFormed = fn;
      distance = fn;
      empty = any;
      name = str;
    };
    # Content (`value`, `contributions`, `shadowed`, `withheld`, `dropped`) is deliberately absent.
    viewRelation = _: {
      name = str;
      definition = el "viewDefinition";
      graph = el "scopeGraph";
    };
    target =
      e:
      if (e.arm or null) == "root" then
        {
          arm = any;
          scope = any;
          channel = any;
        }
      else if (e.arm or null) == "output" then
        {
          arm = any;
          path = any;
        }
      else
        {
          arm = arm [
            "output"
            "root"
          ];
        };
    unit = _: {
      relation = el "viewRelation";
      target = el "target";
      mode = arm placement.modes;
    };
  };

  # The cross-field law a unit carries, decided with its fields (rymxu gate C2): a root target
  # names the channel of the relation it places.
  laws = {
    # The list laws above, over the element's own lists: what the library reads in place of the
    # `member` each of these kinds publishes.
    edgeLabels =
      site: at: e:
      builtins.isList (lettersLaw site "field '${at}.letters'" e.letters);
    relations =
      site: at: e:
      builtins.isList (relationNamesLaw site "field '${at}.names'" e.names);
    relatumLabels =
      site: at: e:
      builtins.isList (relatumNamesLaw site "field '${at}.names'" e.names);
    # A root target's two names are checked by `rootNames`, the one definition its constructor and
    # every root consumer already share (h0e7t), so the refusal is the same one wherever it fires.
    # An output target's path is checked by `tupleKey`'s path position, the guard every output
    # consumer already runs (qf55g), for the same reason.
    target =
      site: _: e:
      if e.arm == "root" then
        builtins.isAttrs (placement.rootNames site e)
      else
        builtins.isString (
          refusal.tupleKey site 1 [
            "out"
            e.path
          ]
        );
    # The constructor's own check, over the element: a fold's seed is its operation's unit.
    viewDefinition =
      site: at: e:
      e.empty == e.combine.unit
      || refuse site "field '${at}.empty' is ${renderValue e.empty}, which is not the unit of the declared combine arm ${renderValue e.combine.arm}; build it with `viewDefinition`";
    unit =
      site: at: e:
      e.target.arm != "root"
      || e.target.channel == e.relation.name
      || refuse site "field '${at}' is a unit whose target names channel ${renderValue e.target.channel} but whose relation is named ${renderValue e.relation.name}; a result lands in the cell it is named for";
  };

  check =
    site: at: kind: e:
    let
      # A kind with no shape is the tag test only (see the header).
      spec = (shapes.${kind} or (_: { })) e;
      one =
        n:
        let
          s = spec.${n};
          p = "${at}.${n}";
        in
        if !(e ? ${n}) then
          refuse site "field '${at}' is a ${kind} element with no '${n}'; build it with `${kind}`"
        else if s ? element then
          elementAt site p s.element e.${n}
        else if s ? arms then
          choice site p s.arms e.${n}
        else if s.ok e.${n} then
          true
        else
          refuse site "field '${p}' is ${renderValue e.${n}}; a ${kind} element's '${n}' is ${s.what}. Build it with `${kind}`";
      fieldsChecked = map one (attrNames spec);
    in
    decided (
      fieldsChecked
      ++ [
        (
          (laws.${kind} or (
            _: _: _:
            true
          )
          )
            site
            at
            e
        )
      ]
    ) e;

  elementAt =
    site: at: element: value:
    if builtins.isAttrs value && (value.__element or null) == element then
      check site at element value
    else
      refuse site "field '${at}' is not a ${element} carrier element (found ${
        if builtins.isAttrs value then
          "an attrset tagged ${renderValue (value.__element or null)}"
        else
          "a ${builtins.typeOf value}"
      }); build it with `${element}` so the element's own refusals have already run";

  # `elementOf site field element value` — unchanged signature and unchanged message for a value
  # that is not tagged at all; a tagged value is now re-checked before it is returned.
  elementOf =
    site: field: element: value:
    elementAt site field element value;

  # `contributionsOf site r` — CONTENT, checked by its reader and only there: a view relation's
  # contributions are a list of records. Forced only where the caller reads them anyway.
  contributionsOf =
    site: r:
    let
      cs = r.contributions;
    in
    if !(builtins.isList cs) then
      refuse site "field 'relation.contributions' is ${renderValue cs}; a view relation's contributions are a list of records"
    else if !(builtins.all builtins.isAttrs cs) then
      refuse site "field 'relation.contributions' carries a non-record; a contribution is a record"
    else
      cs;
in
{
  inherit
    elementOf
    shapes
    contributionsOf
    lettersLaw
    relationNamesLaw
    relatumNamesLaw
    ;
}
