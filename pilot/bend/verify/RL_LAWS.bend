# The claims about the six-rule model in rl.bend. A human states these;
# RL_PROOF.bend proves them, one def per law. See rl_spec.bend for the rule table
# `Rule`, which says what the rules are in terms of fields.
import Base
import ./rl.bend as R
import ./rl_spec.bend as Sp

# A round never loses a triple.
law step_mono:
  for +c: R.Tri
  for +ts: R.Ts
  for p: {R.mem(c, ts) == True{} : Bool}
  {R.mem(c, R.step(ts)) == True{} : Bool}

# Completeness, one law per rule: if the premises are present, the next round has
# the conclusion.
law cax_sco:
  for +c1: Nat
  for +c2: Nat
  for +x: Nat
  for +ts: R.Ts
  for p: {R.mem(R.T{c1, 1n, c2}, ts) == True{} : Bool}
  for q: {R.mem(R.T{x, 0n, c1}, ts) == True{} : Bool}
  {R.mem(R.T{x, 0n, c2}, R.step(ts)) == True{} : Bool}

law scm_sco:
  for +c1: Nat
  for +c2: Nat
  for +c3: Nat
  for +ts: R.Ts
  for p: {R.mem(R.T{c1, 1n, c2}, ts) == True{} : Bool}
  for q: {R.mem(R.T{c2, 1n, c3}, ts) == True{} : Bool}
  {R.mem(R.T{c1, 1n, c3}, R.step(ts)) == True{} : Bool}

law prp_dom:
  for +p: Nat
  for +c: Nat
  for +x: Nat
  for +y: Nat
  for +ts: R.Ts
  for h1: {R.mem(R.T{p, 2n, c}, ts) == True{} : Bool}
  for h2: {R.mem(R.T{x, p, y}, ts) == True{} : Bool}
  {R.mem(R.T{x, 0n, c}, R.step(ts)) == True{} : Bool}

law prp_rng:
  for +p: Nat
  for +c: Nat
  for +x: Nat
  for +y: Nat
  for +ts: R.Ts
  for h1: {R.mem(R.T{p, 3n, c}, ts) == True{} : Bool}
  for h2: {R.mem(R.T{x, p, y}, ts) == True{} : Bool}
  {R.mem(R.T{y, 0n, c}, R.step(ts)) == True{} : Bool}

law prp_inv1:
  for +p1: Nat
  for +p2: Nat
  for +x: Nat
  for +y: Nat
  for +ts: R.Ts
  for h1: {R.mem(R.T{p1, 4n, p2}, ts) == True{} : Bool}
  for h2: {R.mem(R.T{x, p1, y}, ts) == True{} : Bool}
  {R.mem(R.T{y, p2, x}, R.step(ts)) == True{} : Bool}

law prp_inv2:
  for +p1: Nat
  for +p2: Nat
  for +x: Nat
  for +y: Nat
  for +ts: R.Ts
  for h1: {R.mem(R.T{p1, 4n, p2}, ts) == True{} : Bool}
  for h2: {R.mem(R.T{x, p2, y}, ts) == True{} : Bool}
  {R.mem(R.T{y, p1, x}, R.step(ts)) == True{} : Bool}

law prp_trp:
  for +p: Nat
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +ts: R.Ts
  for ht: {R.mem(R.T{p, 0n, 5n}, ts) == True{} : Bool}
  for h1: {R.mem(R.T{x, p, y}, ts) == True{} : Bool}
  for h2: {R.mem(R.T{y, p, z}, ts) == True{} : Bool}
  {R.mem(R.T{x, p, z}, R.step(ts)) == True{} : Bool}

# Soundness: whatever a round has was there already or follows from two triples
# in the graph by one of the rules in the table.
law step_sound:
  for +c: R.Tri
  for +ts: R.Ts
  for p: {R.mem(c, R.step(ts)) == True{} : Bool}
  Or({R.mem(c, ts) == True{} : Bool}, &a: R.Tri -> &b: R.Tri -> ({R.mem(a, ts) == True{} : Bool} & ({R.mem(b, ts) == True{} : Bool} & Sp.Rule(a, b, c, ts))))

# The loop, `iter(n, ts)`: n rounds. It never drops an input triple.
law iter_keeps_input:
  for +n: Nat
  for +ts: R.Ts
  for +c: R.Tri
  for p: {R.mem(c, ts) == True{} : Bool}
  {R.mem(c, R.iter(n, ts)) == True{} : Bool}

# If the stop test `subset(step(r), r)` passes on the result r of n rounds, then
# r is closed under every rule: any conclusion of two triples of r is in r.
law stop_means_closed:
  for +n: Nat
  for +ts: R.Ts
  for +a: R.Tri
  for +b: R.Tri
  for +c: R.Tri
  for stop: {R.subset(R.step(R.iter(n, ts)), R.iter(n, ts)) == True{} : Bool}
  for ha: {R.mem(a, R.iter(n, ts)) == True{} : Bool}
  for hb: {R.mem(b, R.iter(n, ts)) == True{} : Bool}
  for hc: {R.mem(c, R.fire(a, b, R.iter(n, ts))) == True{} : Bool}
  {R.mem(c, R.iter(n, ts)) == True{} : Bool}

# Why a semi-naive round may skip pairs of old triples (the argument behind
# #40's skips). Let `all` be the new triples `delta` in front of the old ones. If
# every firing among old triples is already in `all` (the `sat` test), then
# anything the naive round derives is already in `all` or is derived by a pair
# with a new triple, which is all `derive_semi` fires.
law semi_skip_safe:
  for +old: R.Ts
  for +delta: R.Ts
  for +c: R.Tri
  for sat: {R.subset(R.pairs(old, old, R.append(delta, old)), R.append(delta, old)) == True{} : Bool}
  for p: {R.mem(c, R.derive(R.append(delta, old))) == True{} : Bool}
  Or({R.mem(c, R.append(delta, old)) == True{} : Bool}, {R.mem(c, R.derive_semi(delta, R.append(delta, old))) == True{} : Bool})

# A join against an empty relation fires nothing, so a seed whose partner
# relation is empty may be skipped.
law empty_partner:
  for +xs: R.Ts
  for +c: R.Tri
  for +ts: R.Ts
  {R.mem(c, R.pairs(xs, R.TNil{}, ts)) == False{} : Bool}
