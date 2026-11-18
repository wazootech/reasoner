# The semi-naive skip law's proof: split each premise of a pair into new (delta)
# or old, and for two old premises use rl_semi.bend. Law: semi_skip_safe.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_loop.bend as RLp
import ./rl_pairs.bend as RP
import ./rl_semi.bend as RS

# The semi-naive skip law: split each premise into new (delta) or old.
def semi_b(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), hf: L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old)))), ao: L.Tr(R.mem(a, old)), r: Or(L.Tr(R.mem(b, delta)), L.Tr(R.mem(b, old)))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  match r:
    case Inl{bd}:
      Inr{RM.mem_append_r(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)), R.append(R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)))),
        RM.mem_append_l(c, R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old))),
          RP.pairs_has(a, b, c, R.append(delta, old), delta, R.append(delta, old), RM.mem_append_r(a, delta, old, ao), (bd, hf))))}
    case Inr{bo}:
      RS.semi_old(c, old, delta, a, b, sat, hf, ao, bo)

def semi_a(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), hf: L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old)))), mb: L.Tr(R.mem(b, R.append(delta, old))), r: Or(L.Tr(R.mem(a, delta)), L.Tr(R.mem(a, old)))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  match r:
    case Inl{ad}:
      Inr{RM.mem_append_l(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)), R.append(R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)))),
        RP.pairs_has(a, b, c, delta, R.append(delta, old), R.append(delta, old), ad, (mb, hf)))}
    case Inr{ao}:
      semi_b(c, old, delta, a, b, sat, hf, ao, RM.mem_append_elim(b, delta, old, mb))

def semi_conv(+c: R.Tri, +old: R.Ts, +delta: R.Ts, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), w: RP.WA(c, R.append(delta, old), R.append(delta, old), R.append(delta, old))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  semi_a(c, old, delta, a, b, sat, hf, mb, RM.mem_append_elim(a, delta, old, ma))

def semi_skip(+old: R.Ts, +delta: R.Ts, +c: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), p: L.Tr(R.mem(c, R.derive(R.append(delta, old))))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  semi_conv(c, old, delta, sat, RP.pairs_elim(c, R.append(delta, old), R.append(delta, old), R.append(delta, old), p))

def main() -> U32:
  1
