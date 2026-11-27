# The compose lemmas: if (a, b) and (b, c) are present, composing finds (a, c).
import Base
import ./sco.bend as S
import ./logic.bend as L
import ./mem.bend as M

# compose1_hit: the edge matches, so join_if conses (a, f), which equals (a, d).
def compose1_hit(+a: Nat, +b: Nat, +d: Nat, +c: Nat, +f: Nat, +t: S.Es, hbc: L.Tr(S.neq(b, c)), hdf: L.Tr(S.neq(d, f))) -> L.Tr(S.mem(S.E{a, d}, S.join_if(a, f, S.compose1(S.E{a, b}, t), S.neq(b, c)))):
  %L.join_if_cons(a, f, S.compose1(S.E{a, b}, t), S.neq(b, c), hbc) : L.Tr(S.mem(S.E{a, d}, _))
  L.or_l(S.edge_eq(S.E{a, d}, S.E{a, f}), S.mem(S.E{a, d}, S.compose1(S.E{a, b}, t)), L.and_intro(S.neq(a, a), S.neq(d, f), L.neq_refl(a), hdf))

def compose1_head(+a: Nat, +b: Nat, +d: Nat, +c: Nat, +f: Nat, +t: S.Es, q: L.Tr(S.edge_eq(S.E{b, d}, S.E{c, f}))) -> L.Tr(S.mem(S.E{a, d}, S.join_if(a, f, S.compose1(S.E{a, b}, t), S.neq(b, c)))):
  L.and_elim(S.neq(b, c), S.neq(d, f), q, Unit, Unit{},
    L.Tr(S.mem(S.E{a, d}, S.join_if(a, f, S.compose1(S.E{a, b}, t), S.neq(b, c)))),
    u => hbc => hdf => compose1_hit(a, b, d, c, f, t, hbc, hdf))

# compose1_has: (b, d) in es gives (a, d) in compose1((a, b), es).
def compose1_has(+a: Nat, +b: Nat, +d: Nat, +es: S.Es, p: L.Tr(S.mem(S.E{b, d}, es))) -> L.Tr(S.mem(S.E{a, d}, S.compose1(S.E{a, b}, es))):
  match es:
    case S.ENil{}:
      Empty.absurd(L.Tr(S.mem(S.E{a, d}, S.compose1(S.E{a, b}, S.ENil{}))), L.false_ne_true(p))
    case S.ECons{S.E{+c, +f}, +t}:
      L.or_elim(S.edge_eq(S.E{b, d}, S.E{c, f}), S.mem(S.E{b, d}, t), p, Unit, Unit{},
        L.Tr(S.mem(S.E{a, d}, S.join_if(a, f, S.compose1(S.E{a, b}, t), S.neq(b, c)))),
        u => q => compose1_head(a, b, d, c, f, t, q),
        u => q => M.join_if_keep(S.E{a, d}, a, f, S.compose1(S.E{a, b}, t), S.neq(b, c), compose1_has(a, b, d, t, q)))

# compose_head: the head edge equals (a, b), so compose1 of it finds (a, c).
def compose_head(+a: Nat, +b: Nat, +c: Nat, +h: S.Edge, +t: S.Es, +ys: S.Es, px: L.Tr(S.edge_eq(S.E{a, b}, h)), q: L.Tr(S.mem(S.E{b, c}, ys))) -> L.Tr(S.mem(S.E{a, c}, S.append(S.compose1(h, ys), S.compose(t, ys)))):
  e = L.edge_eq_sound(S.E{a, b}, h, px)
  %e : L.Tr(S.mem(S.E{a, c}, S.append(S.compose1(_, ys), S.compose(t, ys))))
  M.mem_append_l(S.E{a, c}, S.compose1(S.E{a, b}, ys), S.compose(t, ys), compose1_has(a, b, c, ys, q))

# compose_has: (a, b) in xs and (b, c) in ys give (a, c) in compose(xs, ys).
def compose_has(+a: Nat, +b: Nat, +c: Nat, +xs: S.Es, +ys: S.Es, p: L.Tr(S.mem(S.E{a, b}, xs)), q: L.Tr(S.mem(S.E{b, c}, ys))) -> L.Tr(S.mem(S.E{a, c}, S.compose(xs, ys))):
  match xs:
    case S.ENil{}:
      Empty.absurd(L.Tr(S.mem(S.E{a, c}, S.compose(S.ENil{}, ys))), L.false_ne_true(p))
    case S.ECons{+h, +t}:
      L.or_elim(S.edge_eq(S.E{a, b}, h), S.mem(S.E{a, b}, t), p, L.Tr(S.mem(S.E{b, c}, ys)), q,
        L.Tr(S.mem(S.E{a, c}, S.append(S.compose1(h, ys), S.compose(t, ys)))),
        q1 => px => compose_head(a, b, c, h, t, ys, px, q1),
        q1 => pt => M.mem_append_r(S.E{a, c}, S.compose1(h, ys), S.compose(t, ys), compose_has(a, b, c, t, ys, pt, q1)))

def main() -> U32:
  1
