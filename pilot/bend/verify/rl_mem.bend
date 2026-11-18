# Lemmas about membership in the six-rule model's lists (generated from mem.bend
# and elim.bend by renaming Edge to Tri; see rl_logic.bend).
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_logic.bend as RL

def mem_head(+e: R.Tri, +t: R.Ts) -> L.Tr(R.mem(e, R.TCons{e, t})):
  L.or_l(R.tri_eq(e, e), R.mem(e, t), RL.tri_eq_refl(e))

def mem_tail(+e: R.Tri, +h: R.Tri, +t: R.Ts, p: L.Tr(R.mem(e, t))) -> L.Tr(R.mem(e, R.TCons{h, t})):
  L.or_r(R.tri_eq(e, h), R.mem(e, t), p)

def mem_append_l(+e: R.Tri, +xs: R.Ts, +ys: R.Ts, p: L.Tr(R.mem(e, xs))) -> L.Tr(R.mem(e, R.append(xs, ys))):
  match xs:
    case R.TNil{}:
      Empty.absurd(L.Tr(R.mem(e, R.append(R.TNil{}, ys))), L.false_ne_true(p))
    case R.TCons{+h, +t}:
      L.or_elim(R.tri_eq(e, h), R.mem(e, t), p, Unit, Unit{},
        L.Tr(S.or(R.tri_eq(e, h), R.mem(e, R.append(t, ys)))),
        u => q => L.or_l(R.tri_eq(e, h), R.mem(e, R.append(t, ys)), q),
        u => q => L.or_r(R.tri_eq(e, h), R.mem(e, R.append(t, ys)), mem_append_l(e, t, ys, q)))

def mem_append_r(+e: R.Tri, +xs: R.Ts, +ys: R.Ts, p: L.Tr(R.mem(e, ys))) -> L.Tr(R.mem(e, R.append(xs, ys))):
  match xs:
    case R.TNil{}:
      p
    case R.TCons{+h, +t}:
      L.or_r(R.tri_eq(e, h), R.mem(e, R.append(t, ys)), mem_append_r(e, t, ys, p))

# mem_tri_eq: an edge equal to a member of ys is a member of ys.
def mem_tri_eq(+e: R.Tri, +h: R.Tri, +ys: R.Ts, q: L.Tr(R.tri_eq(e, h)), hm: L.Tr(R.mem(h, ys))) -> L.Tr(R.mem(e, ys)):
  eq = RL.tri_eq_sound(e, h, q)
  %Equal.sym(R.Tri, e, h, eq) : L.Tr(R.mem(_, ys))
  hm

def lift_or(+e: R.Tri, +h: R.Tri, +t: R.Ts, +ys: R.Ts, r: Or(L.Tr(R.mem(e, t)), L.Tr(R.mem(e, ys)))) -> Or(L.Tr(R.mem(e, R.TCons{h, t})), L.Tr(R.mem(e, ys))):
  match r:
    case Inl{x}:
      Inl{L.or_r(R.tri_eq(e, h), R.mem(e, t), x)}
    case Inr{y}:
      Inr{y}

# mem_append_elim: a member of xs ++ ys is a member of xs or of ys.
def mem_append_elim(+e: R.Tri, +xs: R.Ts, +ys: R.Ts, p: L.Tr(R.mem(e, R.append(xs, ys)))) -> Or(L.Tr(R.mem(e, xs)), L.Tr(R.mem(e, ys))):
  match xs:
    case R.TNil{}:
      Inr{p}
    case R.TCons{+h, +t}:
      L.or_elim(R.tri_eq(e, h), R.mem(e, R.append(t, ys)), p, Unit, Unit{},
        Or(L.Tr(R.mem(e, R.TCons{h, t})), L.Tr(R.mem(e, ys))),
        u => q => Inl{L.or_l(R.tri_eq(e, h), R.mem(e, t), q)},
        u => q => lift_or(e, h, t, ys, mem_append_elim(e, t, ys, q)))

def main() -> U32:
  1
