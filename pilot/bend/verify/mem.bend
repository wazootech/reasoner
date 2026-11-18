# Lemmas about membership in appended lists and about compose, the heart of
# scm-sco. Everything is stated with `L.Tr(b)`, "the Bool b is True".
import Base
import ./sco.bend as S
import ./logic.bend as L

def mem_head(+e: S.Edge, +t: S.Es) -> L.Tr(S.mem(e, S.ECons{e, t})):
  L.or_l(S.edge_eq(e, e), S.mem(e, t), L.edge_eq_refl(e))

def mem_tail(+e: S.Edge, +h: S.Edge, +t: S.Es, p: L.Tr(S.mem(e, t))) -> L.Tr(S.mem(e, S.ECons{h, t})):
  L.or_r(S.edge_eq(e, h), S.mem(e, t), p)

def mem_append_l(+e: S.Edge, +xs: S.Es, +ys: S.Es, p: L.Tr(S.mem(e, xs))) -> L.Tr(S.mem(e, S.append(xs, ys))):
  match xs:
    case S.ENil{}:
      Empty.absurd(L.Tr(S.mem(e, S.append(S.ENil{}, ys))), L.false_ne_true(p))
    case S.ECons{+h, +t}:
      L.or_elim(S.edge_eq(e, h), S.mem(e, t), p, Unit, Unit{},
        L.Tr(S.or(S.edge_eq(e, h), S.mem(e, S.append(t, ys)))),
        u => q => L.or_l(S.edge_eq(e, h), S.mem(e, S.append(t, ys)), q),
        u => q => L.or_r(S.edge_eq(e, h), S.mem(e, S.append(t, ys)), mem_append_l(e, t, ys, q)))

def mem_append_r(+e: S.Edge, +xs: S.Es, +ys: S.Es, p: L.Tr(S.mem(e, ys))) -> L.Tr(S.mem(e, S.append(xs, ys))):
  match xs:
    case S.ENil{}:
      p
    case S.ECons{+h, +t}:
      L.or_r(S.edge_eq(e, h), S.mem(e, S.append(t, ys)), mem_append_r(e, t, ys, p))

# join_if_keep: join_if only ever adds, so what `rest` has it still has.
def join_if_keep(+x: S.Edge, +a: Nat, +d: Nat, +rest: S.Es, +hit: Bool, p: L.Tr(S.mem(x, rest))) -> L.Tr(S.mem(x, S.join_if(a, d, rest, hit))):
  match hit:
    case True{}:
      mem_tail(x, S.E{a, d}, rest, p)
    case False{}:
      p

def main() -> U32:
  1
