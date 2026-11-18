# Lemmas about `guard` and `one`, the two pieces every rule's conclusion list is
# built from: a guarded singleton.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_logic.bend as RL
import ./rl_mem.bend as RM

# guard_has: a member of xs stays a member when the guard holds.
def guard_has(+hit: Bool, +xs: R.Ts, +c: R.Tri, h: L.Tr(hit), p: L.Tr(R.mem(c, xs))) -> L.Tr(R.mem(c, R.guard(hit, xs))):
  match hit:
    case True{}:
      p
    case False{}:
      Empty.absurd(L.Tr(R.mem(c, R.guard(False{}, xs))), L.false_ne_true(h))

# guard_elim: a member of guard(hit, xs) needs `hit`, and is a member of xs.
def guard_elim(+hit: Bool, +xs: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.guard(hit, xs))), -P: Type, k: L.Tr(hit) -> L.Tr(R.mem(c, xs)) -> P) -> P:
  match hit:
    case True{}:
      k({==}, p)
    case False{}:
      Empty.absurd(P, L.false_ne_true(p))

# one_has: the singleton holds its own triple.
def one_has(+x: R.Tri) -> L.Tr(R.mem(x, R.one(x))):
  L.or_l(R.tri_eq(x, x), R.mem(x, R.TNil{}), RL.tri_eq_refl(x))

# one_elim: a member of the singleton [x] is x.
def one_elim(+c: R.Tri, +x: R.Tri, p: L.Tr(R.mem(c, R.one(x)))) -> {c == x : R.Tri}:
  L.or_elim(R.tri_eq(c, x), R.mem(c, R.TNil{}), p, Unit, Unit{}, {c == x : R.Tri},
    u => q => RL.tri_eq_sound(c, x, q),
    u => q => Empty.absurd({c == x : R.Tri}, L.false_ne_true(q)))

def main() -> U32:
  1
