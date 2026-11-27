# Lemmas about the stop test and iter in the six-rule model (from loop.bend).
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_logic.bend as RL
import ./rl_dedupe.bend as RD

# The context is (h in ys) and (t is a subset of ys); each branch uses one half.
def Ctx(+h: R.Tri, +t: R.Ts, +ys: R.Ts) -> Type:
  L.Tr(R.mem(h, ys)) & L.Tr(R.subset(t, ys))

def ctx_fst(+h: R.Tri, +t: R.Ts, +ys: R.Ts, c: Ctx(h, t, ys)) -> L.Tr(R.mem(h, ys)):
  (x, y) = c
  x

def ctx_snd(+h: R.Tri, +t: R.Ts, +ys: R.Ts, c: Ctx(h, t, ys)) -> L.Tr(R.subset(t, ys)):
  (x, y) = c
  y

# sub_elim: if `subset(xs, ys)` holds, every member of xs is a member of ys.
def sub_elim(+e: R.Tri, +xs: R.Ts, +ys: R.Ts, hs: L.Tr(R.subset(xs, ys)), p: L.Tr(R.mem(e, xs))) -> L.Tr(R.mem(e, ys)):
  match xs:
    case R.TNil{}:
      Empty.absurd(L.Tr(R.mem(e, ys)), L.false_ne_true(p))
    case R.TCons{+h, +t}:
      L.and_elim(R.mem(h, ys), R.subset(t, ys), hs, L.Tr(R.mem(e, R.TCons{h, t})), p, L.Tr(R.mem(e, ys)),
        p1 => hm => hst => L.or_elim(R.tri_eq(e, h), R.mem(e, t), p1, Ctx(h, t, ys), (hm, hst), L.Tr(R.mem(e, ys)),
          c => q => RM.mem_tri_eq(e, h, ys, q, ctx_fst(h, t, ys, c)),
          c => q => sub_elim(e, t, ys, ctx_snd(h, t, ys, c), q)))

# iter_contains: n rounds keep every input edge.
def iter_contains(+n: Nat, +es: R.Ts, +e: R.Tri, p: L.Tr(R.mem(e, es))) -> L.Tr(R.mem(e, R.iter(n, es))):
  match n:
    case 0n:
      p
    case 1n+q:
      RD.union_keeps(e, R.derive(R.iter(q, es)), R.iter(q, es), iter_contains(q, es, e, p))

def main() -> U32:
  1
