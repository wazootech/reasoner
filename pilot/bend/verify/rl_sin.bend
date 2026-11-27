# derive_semi fires only what naive derive fires: semi_in_derive. So a semi-naive
# round never invents a triple the naive round would not.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_guard.bend as RG
import ./rl_pairs.bend as RP

def sid_p1(+c: R.Tri, +delta: R.Ts, +old: R.Ts, w: RP.WA(c, delta, R.append(delta, old), R.append(delta, old))) -> L.Tr(R.mem(c, R.derive(R.append(delta, old)))):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  RP.pairs_has(a, b, c, R.append(delta, old), R.append(delta, old), R.append(delta, old), RM.mem_append_l(a, delta, old, ma), (mb, hf))

def sid_p2(+c: R.Tri, +delta: R.Ts, +old: R.Ts, w: RP.WA(c, R.append(delta, old), delta, R.append(delta, old))) -> L.Tr(R.mem(c, R.derive(R.append(delta, old)))):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  RP.pairs_has(a, b, c, R.append(delta, old), R.append(delta, old), R.append(delta, old), ma, (RM.mem_append_l(b, delta, old, mb), hf))

def sid_g(+c: R.Tri, +delta: R.Ts, +old: R.Ts, q: L.Tr(R.mem(c, R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)))))) -> L.Tr(R.mem(c, R.derive(R.append(delta, old)))):
  RG.guard_elim(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)), c, q, L.Tr(R.mem(c, R.derive(R.append(delta, old)))), h => m => m)

def sid_r2(+c: R.Tri, +delta: R.Ts, +old: R.Ts, r: Or(L.Tr(R.mem(c, R.pairs(R.append(delta, old), delta, R.append(delta, old)))), L.Tr(R.mem(c, R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old))))))) -> L.Tr(R.mem(c, R.derive(R.append(delta, old)))):
  match r:
    case Inl{x}:
      sid_p2(c, delta, old, RP.pairs_elim(c, R.append(delta, old), delta, R.append(delta, old), x))
    case Inr{y}:
      sid_g(c, delta, old, y)

def sid_r1(+c: R.Tri, +delta: R.Ts, +old: R.Ts, r: Or(L.Tr(R.mem(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)))), L.Tr(R.mem(c, R.append(R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)))))))) -> L.Tr(R.mem(c, R.derive(R.append(delta, old)))):
  match r:
    case Inl{x}:
      sid_p1(c, delta, old, RP.pairs_elim(c, delta, R.append(delta, old), R.append(delta, old), x))
    case Inr{y}:
      sid_r2(c, delta, old, RM.mem_append_elim(c, R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old))), y))

# semi_in_derive: a triple derive_semi fires is one derive fires.
def semi_in_derive(+c: R.Tri, +delta: R.Ts, +old: R.Ts, q: L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))) -> L.Tr(R.mem(c, R.derive(R.append(delta, old)))):
  sid_r1(c, delta, old, RM.mem_append_elim(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)), R.append(R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)))), q))

def main() -> U32:
  1
