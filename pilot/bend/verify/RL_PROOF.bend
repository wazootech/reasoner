# Proofs of RL_LAWS.bend. `bend RL_PROOF.bend --verdict` is the gate.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./RL_LAWS.bend as Laws
import ./rl_mem.bend as RM
import ./rl_dedupe.bend as RD
import ./rl_loop.bend as RLp
import ./rl_pairs.bend as RP
import ./rl_rules.bend as RR
import ./rl_spec.bend as Sp

# closes: a, b in the graph and c in fire(a, b) put c in the next round.
def closes(+a: R.Tri, +b: R.Tri, +c: R.Tri, +ts: R.Ts, ha: L.Tr(R.mem(a, ts)), hb: L.Tr(R.mem(b, ts)), hc: L.Tr(R.mem(c, R.fire(a, b, ts)))) -> L.Tr(R.mem(c, R.step(ts))):
  RD.union_has(c, R.derive(ts), ts, RP.pairs_has(a, b, c, ts, ts, ts, ha, (hb, hc)))

def Laws.step_mono(c, ts, p):
  RD.union_keeps(c, R.derive(ts), ts, p)

def Laws.cax_sco(c1, c2, x, ts, p, q):
  closes(R.T{c1, 1n, c2}, R.T{x, 0n, c1}, R.T{x, 0n, c2}, ts, p, q,
    RR.has1(R.T{c1, 1n, c2}, R.T{x, 0n, c1}, ts, L.neq_refl(c1)))

def Laws.scm_sco(c1, c2, c3, ts, p, q):
  closes(R.T{c1, 1n, c2}, R.T{c2, 1n, c3}, R.T{c1, 1n, c3}, ts, p, q,
    RR.has2(R.T{c1, 1n, c2}, R.T{c2, 1n, c3}, ts, L.neq_refl(c2)))

def Laws.prp_dom(p, c, x, y, ts, h1, h2):
  closes(R.T{p, 2n, c}, R.T{x, p, y}, R.T{x, 0n, c}, ts, h1, h2,
    RR.has3(R.T{p, 2n, c}, R.T{x, p, y}, ts, L.neq_refl(p)))

def Laws.prp_rng(p, c, x, y, ts, h1, h2):
  closes(R.T{p, 3n, c}, R.T{x, p, y}, R.T{y, 0n, c}, ts, h1, h2,
    RR.has4(R.T{p, 3n, c}, R.T{x, p, y}, ts, L.neq_refl(p)))

def Laws.prp_inv1(p1, p2, x, y, ts, h1, h2):
  closes(R.T{p1, 4n, p2}, R.T{x, p1, y}, R.T{y, p2, x}, ts, h1, h2,
    RR.has5(R.T{p1, 4n, p2}, R.T{x, p1, y}, ts, L.neq_refl(p1)))

def Laws.prp_inv2(p1, p2, x, y, ts, h1, h2):
  closes(R.T{p1, 4n, p2}, R.T{x, p2, y}, R.T{y, p1, x}, ts, h1, h2,
    RR.has6(R.T{p1, 4n, p2}, R.T{x, p2, y}, ts, L.neq_refl(p2)))

def Laws.prp_trp(p, x, y, z, ts, ht, h1, h2):
  closes(R.T{x, p, y}, R.T{y, p, z}, R.T{x, p, z}, ts, h1, h2,
    RR.has7(R.T{x, p, y}, R.T{y, p, z}, ts,
      L.and_intro(S.and(S.neq(p, p), S.neq(y, y)), R.mem(R.T{p, 0n, 5n}, ts),
        L.and_intro(S.neq(p, p), S.neq(y, y), L.neq_refl(p), L.neq_refl(y)), ht)))

# conv turns pairs_elim's witnesses into the law's form, through the rule table.
def conv(+c: R.Tri, +ts: R.Ts, w: RP.WA(c, ts, ts, ts)) -> &a: R.Tri -> &b: R.Tri -> (L.Tr(R.mem(a, ts)) & (L.Tr(R.mem(b, ts)) & Sp.Rule(a, b, c, ts))):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  (a, (b, (ma, (mb, RR.rule_sound(a, b, ts, c, RR.fire_cases(a, b, ts, c, hf))))))

def sound_cases(+c: R.Tri, +ts: R.Ts, r: Or(L.Tr(R.mem(c, R.derive(ts))), L.Tr(R.mem(c, ts)))) -> Or(L.Tr(R.mem(c, ts)), &a: R.Tri -> &b: R.Tri -> (L.Tr(R.mem(a, ts)) & (L.Tr(R.mem(b, ts)) & Sp.Rule(a, b, c, ts)))):
  match r:
    case Inl{y}:
      Inr{conv(c, ts, RP.pairs_elim(c, ts, ts, ts, y))}
    case Inr{x}:
      Inl{x}

def Laws.step_sound(c, ts, p):
  sound_cases(c, ts, RD.union_elim(c, R.derive(ts), ts, p))

def Laws.iter_keeps_input(n, ts, c, p):
  RLp.iter_contains(n, ts, c, p)

def Laws.stop_means_closed(n, ts, a, b, c, stop, ha, hb, hc):
  RLp.sub_elim(c, R.step(R.iter(n, ts)), R.iter(n, ts), stop, closes(a, b, c, R.iter(n, ts), ha, hb, hc))

# The semi-naive skip law: split each premise into new (delta) or old.
def semi_b(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, R.append(delta, old)), R.append(delta, old))), hf: L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old)))), ao: L.Tr(R.mem(a, old)), r: Or(L.Tr(R.mem(b, delta)), L.Tr(R.mem(b, old)))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  match r:
    case Inl{bd}:
      Inr{RM.mem_append_r(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)), R.pairs(R.append(delta, old), delta, R.append(delta, old)),
        RP.pairs_has(a, b, c, R.append(delta, old), delta, R.append(delta, old), RM.mem_append_r(a, delta, old, ao), (bd, hf)))}
    case Inr{bo}:
      Inl{RLp.sub_elim(c, R.pairs(old, old, R.append(delta, old)), R.append(delta, old), sat,
        RP.pairs_has(a, b, c, old, old, R.append(delta, old), ao, (bo, hf)))}

def semi_a(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, R.append(delta, old)), R.append(delta, old))), hf: L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old)))), mb: L.Tr(R.mem(b, R.append(delta, old))), r: Or(L.Tr(R.mem(a, delta)), L.Tr(R.mem(a, old)))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  match r:
    case Inl{ad}:
      Inr{RM.mem_append_l(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)), R.pairs(R.append(delta, old), delta, R.append(delta, old)),
        RP.pairs_has(a, b, c, delta, R.append(delta, old), R.append(delta, old), ad, (mb, hf)))}
    case Inr{ao}:
      semi_b(c, old, delta, a, b, sat, hf, ao, RM.mem_append_elim(b, delta, old, mb))

def semi_conv(+c: R.Tri, +old: R.Ts, +delta: R.Ts, sat: L.Tr(R.subset(R.pairs(old, old, R.append(delta, old)), R.append(delta, old))), w: RP.WA(c, R.append(delta, old), R.append(delta, old), R.append(delta, old))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  semi_a(c, old, delta, a, b, sat, hf, mb, RM.mem_append_elim(a, delta, old, ma))

def Laws.semi_skip_safe(old, delta, c, sat, p):
  semi_conv(c, old, delta, sat, RP.pairs_elim(c, R.append(delta, old), R.append(delta, old), R.append(delta, old), p))

def Laws.empty_partner(xs, c, ts):
  match xs:
    case R.TNil{}:
      {==}
    case R.TCons{h, t}:
      Laws.empty_partner(t, c, ts)
