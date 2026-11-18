# The loop's lemmas: the stop test `subset` is sound, and `iter` keeps its input.
import Base
import ./sco.bend as S
import ./logic.bend as L
import ./mem.bend as M

# hit: an edge equal to a member of ys is a member of ys.
def hit(+e: S.Edge, +h: S.Edge, +ys: S.Es, q: L.Tr(S.edge_eq(e, h)), hm: L.Tr(S.mem(h, ys))) -> L.Tr(S.mem(e, ys)):
  eq = L.edge_eq_sound(e, h, q)
  %Equal.sym(S.Edge, e, h, eq) : L.Tr(S.mem(_, ys))
  hm

# The context is (h in ys) and (t is a subset of ys); each branch uses one half.
def Ctx(+h: S.Edge, +t: S.Es, +ys: S.Es) -> Type:
  L.Tr(S.mem(h, ys)) & L.Tr(S.subset(t, ys))

def ctx_fst(+h: S.Edge, +t: S.Es, +ys: S.Es, c: Ctx(h, t, ys)) -> L.Tr(S.mem(h, ys)):
  (x, y) = c
  x

def ctx_snd(+h: S.Edge, +t: S.Es, +ys: S.Es, c: Ctx(h, t, ys)) -> L.Tr(S.subset(t, ys)):
  (x, y) = c
  y

# sub_elim: if `subset(xs, ys)` holds, every member of xs is a member of ys.
def sub_elim(+e: S.Edge, +xs: S.Es, +ys: S.Es, hs: L.Tr(S.subset(xs, ys)), p: L.Tr(S.mem(e, xs))) -> L.Tr(S.mem(e, ys)):
  match xs:
    case S.ENil{}:
      Empty.absurd(L.Tr(S.mem(e, ys)), L.false_ne_true(p))
    case S.ECons{+h, +t}:
      L.and_elim(S.mem(h, ys), S.subset(t, ys), hs, L.Tr(S.mem(e, S.ECons{h, t})), p, L.Tr(S.mem(e, ys)),
        p1 => hm => hst => L.or_elim(S.edge_eq(e, h), S.mem(e, t), p1, Ctx(h, t, ys), (hm, hst), L.Tr(S.mem(e, ys)),
          c => q => hit(e, h, ys, q, ctx_fst(h, t, ys, c)),
          c => q => sub_elim(e, t, ys, ctx_snd(h, t, ys, c), q)))

# iter_contains: n rounds keep every input edge.
def iter_contains(+n: Nat, +es: S.Es, +e: S.Edge, p: L.Tr(S.mem(e, es))) -> L.Tr(S.mem(e, S.iter(n, es))):
  match n:
    case 0n:
      p
    case 1n+q:
      M.mem_append_l(e, S.iter(q, es), S.compose(S.iter(q, es), S.iter(q, es)), iter_contains(q, es, e, p))

def main() -> U32:
  1
