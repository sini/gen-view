# THE MOVEMENT ORACLE — THE v1 ARMS OF THE ACCEPTANCE CORPUS.
#
# The movement spec §12.6 names enumerating the corpus a stated input to AC-7, and AC-7 ran over it
# on 2026-08-20 (spec §9.5). What survives here is its third stratum: the six measured den v1 arms
# A–F, re-expressed as gen-view declarations. Its first two strata (the fixture's declaration shapes
# and the spec's acceptance topologies) were the subject of O1 — the totality of the map into the
# frozen edge record — and left with that map when the edge record's library retired (ADR-0010 §3).
#
# den v1's own source is not opened: the six arms' answers are quoted from the 2026-08-06
# measurement record and re-expressed, exactly as the movement spec's §12 does.
{ genView, genScope }:
let
  v = genView;

  # ── S3 — THE v1 ARMS' SHARED SHAPE ──────────────────────────────────────────────────────────
  # `F --P--> H --P--> U` in the measurement record's notation. Re-expressed with `parent` as the
  # STRUCTURAL letter and the four binding-kinds as names in R, which is the scoped-relations
  # arrangement gen-view's own fixture header states. Edges are child → parent, so an OUTBOUND walk
  # from `U` reaches `H` at one hop and `F` at two.
  v1Labels = v.edgeLabels { letters = [ "parent" ]; };
  v1Relations = v.relations {
    names = [
      "import"
      "expose-in"
      "broadcast-in"
      "policy"
    ];
  };
  v1Roles = v.relatumLabels { names = [ ]; };
  v1Admission = genScope.wellFormed {
    alphabet = v1Labels.letters;
    expression = "parent*";
  };
  # ONE layer, so no letter outranks another; `endOfPath = -1` ranks stopping ABOVE continuing,
  # which is Fig. 1's rule 2 (`$ <l l ⊢ s <p s·l·p`) and is what makes the NEARER arrival win.
  v1Order = genScope.labelOrder {
    alphabet = v1Labels.letters;
    layers = [ [ "parent" ] ];
    endOfPath = -1;
  };
  # THE IDENTITY ORDER MARK over the arms' one letter: `$` tied with `parent`, so the lexicographic
  # product degenerates to `v1Order` and the arms measure the declaration's own order exactly.
  v1Mark = genScope.labelOrder {
    alphabet = v1Labels.letters;
    layers = [ [ "parent" ] ];
    endOfPath = 0;
  };
  v1Carrier = v.carrier {
    labels = v1Labels;
    relations = v1Relations;
    relatumLabels = v1Roles;
    labelWellFormedness = v1Admission;
    labelOrder = v1Order;
    dataOrder = v.dataOrder {
      channel = "pipe";
      keyOf = _: "pipe";
    };
  };
  v1Scopes = [
    "U"
    "H"
    "F"
  ];
  v1Edges.parent =
    id:
    {
      U = [ "H" ];
      H = [ "F" ];
    }
    .${id} or [ ];

  v1Graph =
    data:
    v.scopeGraph {
      carrier = v1Carrier;
      scopes = v1Scopes;
      edges = v1Edges;
      inherit data;
    };

  v1Definition =
    relation:
    v.compositions.movement {
      channel = "pipe";
      inherit relation;
      root = "U";
      direction = "outbound";
      admission = v1Admission;
      order = v1Order;
      wellFormed = _: true;
      tieSet = v.tieSets.union;
      empty = [ ];
      combine = v.combines.listAppend;
      dedup = v.dedups.none;
    };

  v1Run =
    {
      relation,
      data,
    }:
    v.viewRelation {
      engine = genScope;
      definition = v1Definition relation;
      graph = v1Graph data;
      marks = _: [ ];
      orderMark = v1Mark;
    };

  # ── S3 — THE SIX v1 ARMS ────────────────────────────────────────────────────────────────────
  # Each arm's v1 answer is quoted from `2026-08-06-movement-specificity-measurement.md` §6.1's
  # verbatim probe output. `expressible = false` arms carry the reason and no result.
  armA = v1Run {
    relation = "policy";
    data = [
      {
        scope = "H";
        relation = "policy";
        datum = [ "H-val" ];
      }
      {
        scope = "F";
        relation = "policy";
        datum = [ "F-val" ];
      }
    ];
  };

  armC = v1Run {
    relation = "policy";
    data = [
      {
        scope = "H";
        relation = "expose-in";
        datum = [ "S-exposed" ];
      }
      {
        scope = "F";
        relation = "policy";
        datum = [ "F-val" ];
      }
    ];
  };

  armE = v1Run {
    relation = "policy";
    data = [
      {
        scope = "H";
        relation = "expose-in";
        datum = [ "S-exposed" ];
      }
      {
        scope = "H";
        relation = "policy";
        datum = [ "S-exposed" ];
      }
      {
        scope = "F";
        relation = "policy";
        datum = [ "F-val" ];
      }
    ];
  };

  # Arm B's two halves, each a declaration of its own — which IS the finding: v1 decides them
  # against each other and one declaration cannot.
  armBbroadcast = v1Run {
    relation = "broadcast-in";
    data = [
      {
        scope = "U";
        relation = "broadcast-in";
        datum = [ "B-broadcast-val" ];
      }
      {
        scope = "H";
        relation = "policy";
        datum = [ "H-policy-val" ];
      }
    ];
  };
  armBpolicy = v1Run {
    relation = "policy";
    data = [
      {
        scope = "U";
        relation = "broadcast-in";
        datum = [ "B-broadcast-val" ];
      }
      {
        scope = "H";
        relation = "policy";
        datum = [ "H-policy-val" ];
      }
    ];
  };

  arms = {
    A = {
      expressible = true;
      v1 = [ "H-val" ];
      result = armA;
      note = "CONTROL. Same relation at two distances; the nearer arrival wins by Fig. 1's rule 2 (`$ <l parent`), so this arm discriminates by path length exactly as v1 discriminates by hop count.";
    };
    B = {
      expressible = false;
      v1 = [ "B-broadcast-val" ];
      halves = {
        broadcastIn = armBbroadcast;
        policy = armBpolicy;
      };
      reason = "CROSS-RELATION CONTENTION. v1 groups a `broadcast-in` datum at distance 0 against a `policy` datum at distance 1 and decides between them. A gen-view `viewDefinition` names EXACTLY ONE relation `r` (`lib/definition.nix`: `relation` is a non-empty string, and `relationLookup` filters `entry.relation == r`), so the two candidates are reached by two DIFFERENT declarations and never compete. The competition key `k` groups within one declaration's contributions; it cannot group across two.";
    };
    C = {
      expressible = true;
      v1 = [ "F-val" ];
      result = armC;
      note = "THE DISCRIMINATOR, AND IT FALLS OUT RATHER THAN BEING ARRANGED. `H` holds only an `expose-in` datum, so under (NR-Rel) a view ABOUT `policy` finds nothing at `H` and the walk's answer at `H` contributes nothing — 'the nearer differently-labelled node is invisible, not outranked' is what the relation filter DOES, not something the order has to be tuned to reproduce.";
    };
    D = {
      expressible = false;
      v1 = [
        "H-own-import"
        "S-exposed-up"
        "K-broadcast-in"
      ];
      reason = "CROSS-RELATION UNION. Four binding-kinds at ONE node, unioned at equal distance. Three distinct relation names, so three declarations; one declaration reaches one relation's datums and the union across kinds is not a movement result but a join of three.";
    };
    E = {
      expressible = true;
      v1 = [ "S-exposed" ];
      result = armE;
      note = "CONTROL FOR C. One label flipped at `H` — `H` gains a `policy` datum — and the answer flips to the nearer node's. C and E differ in exactly that one datum's relation, so C's answer is caused by `H`'s missing `policy` and by nothing else, at the destination as at v1.";
    };
    F = {
      expressible = false;
      v1 = [ "N-self-only-reemit" ];
      reason = "CROSS-RELATION CONTENTION, same cause as B: an own-`import` at distance 0 against a `policy` at distance 1. ★ AND THIS ARM LEFT THE ACCEPTANCE ITEM: movement spec revision 2 strikes 'arm F reproduces F1' from AC-3's failure column and assigns the arm's disposition elsewhere, so its inexpressibility here is not adjudicated by this measurement either.";
    };
  };

in
{
  inherit
    arms
    v1Run
    v1Definition
    v1Graph
    v1Labels
    v1Order
    v1Admission
    v1Carrier
    ;
}
