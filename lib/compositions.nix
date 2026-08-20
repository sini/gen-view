# THE NAMED COMPOSITIONS — one construction under five names.
#
# ★★ THE LAW THIS LIBRARY IS AN INSTANCE OF, NOT AN EXCEPTION TO: EVERY DERIVED VIEW IS A NAMED
# MATERIALIZED QUERY RESULT OVER THE SELECTOR ALGEBRA, and registry, topology, channel, role and
# the aspect/entity classification itself are ONE CONSTRUCTION UNDER DIFFERENT NAMES. Movement is
# the FIRST composition over the calculus, not the calculus.
#
# ★★ AND THE AXIS THEY DIFFER ON IS EXACTLY ONE: THE COMPETITION KEY. A channel competes per
# channel, a registry per entity, a topology per scope, a role per role name. Everything else —
# the alphabet, the path expression, the label order, the relation reached at the end, the tie-set
# disposition, the fold — is the same construction reading the same carrier. Publishing five
# mechanisms where there is one key would be the coupling-through-misscoping this library exists to
# avoid; publishing five NAMES over one mechanism is the vocabulary claim it exists to make.
#
# ★ A PROJECTION HAS A NAME AND A DEFINING QUERY, OR IT IS NOT A VIEW. That is the ruled
# sharpening of "projections, never sources": a framework's flat registry and a schema's edge and
# topology attributes are PROJECTIONS of the graph and never SOURCES for it, so each of them owes a
# name and a defining query here rather than a private accumulation elsewhere.
#
# ★ WHAT THE COMPOSITIONS SUPPLY AND WHAT THEY DO NOT. Each supplies the DISTANCE RULE — movement's
# instance is plain hop count — and the competition key derived from its own axis. Each leaves WFD
# to the caller, because "what you were looking for" is the caller's question and not the
# composition's. NOTHING IS DEFAULTED IN THE SUBSTRATE: a composition STATING an instance is
# visible in its own source, where a substrate default is a decision nobody made and nobody can see.
#
# ★★ AND THE COMPOSITIONS CONSTRUCT OVER THE PUBLISHED RAW EXPORTS, not over a parallel private
# surface. That is the property that makes the raw layer load-bearing rather than decorative: if
# the compositions reached past the published elements into a private twin, the raw layer would be
# a second surface nobody uses and the calculus would be hidden again.
{ prelude, graph }:
let
  refusal = import ./refusal.nix { inherit prelude; };
  carrierLib = import ./carrier.nix { inherit prelude graph; };
  definitionLib = import ./definition.nix { inherit prelude graph; };
  inherit (refusal) refuse fields;
  inherit (carrierLib) dataOrder;
  inherit (definitionLib) viewDefinition;

  # The fields every composition takes. R§2.10's declaration fields, plus the relation the view is
  # ABOUT (the scoped-relations obligation: a declaration that could not name a relation would have
  # recorded that ruling and not built it) and WFD.
  common = [
    "channel"
    "relation"
    "root"
    "direction"
    "admission"
    "order"
    "wellFormed"
    "tieSet"
    "empty"
    "combine"
    "dedup"
  ];

  # PLAIN HOP COUNT — movement's instance of the distance rule, and the shared instance of every
  # composition here. A composition whose carrier reifies a relation as a node would charge that
  # hop zero, which is exactly why the rule is a parameter and not a constant in the substrate.
  hopCount = s: s.distance + 1;

  define =
    site: extra: keyOfFor: args:
    let
      a = fields site (common ++ extra) args;
    in
    if !(builtins.isString a.channel) || a.channel == "" then
      refuse site "field 'channel' must be a non-empty name; a projection has a NAME and a defining query, or it is not a view"
    else
      viewDefinition (
        (builtins.removeAttrs a extra)
        // {
          channel = dataOrder {
            inherit (a) channel;
            keyOf = keyOfFor a;
          };
          distance = hopCount;
        }
      );

  compositions = {
    # ── MOVEMENT — the first composition ──
    # Competition is per CHANNEL: everything that reaches this channel competes with everything
    # else that reaches it, which is what makes shadowing mean anything at all.
    movement = define "compositions.movement" [ ] (a: _: a.channel);

    # ── CHANNEL — the seed instance ──
    # "A channel is a named, materialized query result" is the general law in miniature, ruled for
    # a single view. ★ IT IS THE SAME CONSTRUCTION AS MOVEMENT AND IS PUBLISHED AS SUCH: treating
    # the seed instance as a distinct mechanism is precisely the error the generalization corrects,
    # so this name is a vocabulary claim over one construction and not a second implementation of
    # it. What it buys is that the retiring surface's `channel` has a name here to become
    # expressible under.
    channel = define "compositions.channel" [ ] (a: _: a.channel);

    # ── REGISTRY — competition per ENTITY ──
    # A flat registry is a projection of the graph. Its competition key is the entity, so two
    # contributions about one entity compete and two about different entities do not — which is
    # the property a registry has and a channel does not.
    registry = define "compositions.registry" [ "entityOf" ] (a: c: a.entityOf c);

    # ── TOPOLOGY — competition per SCOPE ──
    # A topology attribute is a projection of the graph's own edge structure: what competes is what
    # is said ABOUT one scope, so the key is the scope the contribution was reached at.
    topology = define "compositions.topology" [ ] (_: c: c.scope);

    # ── ROLE — competition per ROLE NAME ──
    role = define "compositions.role" [ "roleOf" ] (a: c: a.roleOf c);
  };
in
{
  inherit compositions common hopCount;
}
