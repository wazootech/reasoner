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
import ./rl_semi.bend as RS
import ./rl_skip.bend as RK
import ./rl_least.bend as RLe
import ./rl_semiloop.bend as RSl
import ./rl_final.bend as RFi
import ./rl_sub.bend as Sb

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

def Laws.semi_skip_safe(old, delta, c, sat, p):
  RK.semi_skip(old, delta, c, sat, p)

def Laws.empty_partner(xs, c, ts):
  match xs:
    case R.TNil{}:
      {==}
    case R.TCons{h, t}:
      Laws.empty_partner(t, c, ts)

def Laws.least_closure(n, ts, s, hsub, hst):
  RLe.iter_least(n, ts, s, hsub, RS.dup(Bool, R.subset(R.step(s), s), True{}, hst))

def Laws.semi_keeps_input(n, ts, c, p):
  RSl.iter_semi_keeps(n, R.TNil{}, ts, c, RM.mem_append_l(c, ts, R.TNil{}, p))

def Laws.semi_stop_closed(n, ts, a, b, c, fixed, ha, hb, hc):
  RSl.iter_semi_closed(n, R.TNil{}, ts, a, b, c, {==}, fixed, ha, hb, hc)

def Laws.semi_least(n, ts, s, hsub, hst):
  RSl.iter_semi_least(n, R.TNil{}, ts, s,
    L.and_intro(R.subset(R.append(ts, R.TNil{}), s), R.subset(R.step(s), s), Sb.subset_append(ts, R.TNil{}, s, hsub, {==}), hst))

def Laws.semi_equals_naive(n, m, ts, stop, fixed):
  (c => p => RLp.sub_elim(c, R.iter(n, ts), R.iter_semi(m, R.TNil{}, ts), RFi.naive_in_semi(n, m, ts, fixed), p),
   c => p => RLp.sub_elim(c, R.iter_semi(m, R.TNil{}, ts), R.iter(n, ts), RFi.semi_in_naive(n, m, ts, stop), p))
