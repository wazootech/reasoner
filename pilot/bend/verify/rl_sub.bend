# Lemmas about `subset` and the `fresh_go` that a semi-naive round uses.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_logic.bend as RL
import ./rl_mem.bend as RM
import ./rl_dedupe.bend as RD

# subset_cons: a subset of ys is a subset of ys with something added.
def subset_cons(+xs: R.Ts, +ys: R.Ts, +h: R.Tri, hs: L.Tr(R.subset(xs, ys))) -> L.Tr(R.subset(xs, R.TCons{h, ys})):
  match xs:
    case R.TNil{}:
      {==}
    case R.TCons{+x, +t}:
      L.and_elim(R.mem(x, ys), R.subset(t, ys), hs, Unit, Unit{}, L.Tr(R.subset(R.TCons{x, t}, R.TCons{h, ys})),
        u => hm => hst => L.and_intro(R.mem(x, R.TCons{h, ys}), R.subset(t, R.TCons{h, ys}), RM.mem_tail(x, h, ys, hm), subset_cons(t, ys, h, hst)))

def subset_refl(+l: R.Ts) -> L.Tr(R.subset(l, l)):
  match l:
    case R.TNil{}:
      {==}
    case R.TCons{+h, +t}:
      L.and_intro(R.mem(h, R.TCons{h, t}), R.subset(t, R.TCons{h, t}), RM.mem_head(h, t), subset_cons(t, t, h, subset_refl(t)))

# subset_append: both halves in S puts the whole in S.
def subset_append(+xs: R.Ts, +ys: R.Ts, +s: R.Ts, hx: L.Tr(R.subset(xs, s)), hy: L.Tr(R.subset(ys, s))) -> L.Tr(R.subset(R.append(xs, ys), s)):
  match xs:
    case R.TNil{}:
      hy
    case R.TCons{+h, +t}:
      L.and_elim(R.mem(h, s), R.subset(t, s), hx, L.Tr(R.subset(ys, s)), hy, L.Tr(R.subset(R.append(R.TCons{h, t}, ys), s)),
        hy1 => hm => hst => L.and_intro(R.mem(h, s), R.subset(R.append(t, ys), s), hm, subset_append(t, ys, s, hst, hy1)))

def main() -> U32:
  1
