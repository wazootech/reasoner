# Elimination lemmas: what membership in `append`, `join_if`, `compose1` and
# `compose` tells you. They are the soundness half of scm-sco: nothing is added
# that is not a composition of two present edges.
import Base
import ./sco.bend as S
import ./logic.bend as L
import ./mem.bend as M

def lift_or(+e: S.Edge, +h: S.Edge, +t: S.Es, +ys: S.Es, r: Or(L.Tr(S.mem(e, t)), L.Tr(S.mem(e, ys)))) -> Or(L.Tr(S.mem(e, S.ECons{h, t})), L.Tr(S.mem(e, ys))):
  match r:
    case Inl{x}:
      Inl{L.or_r(S.edge_eq(e, h), S.mem(e, t), x)}
    case Inr{y}:
      Inr{y}

# mem_append_elim: a member of xs ++ ys is a member of xs or of ys.
def mem_append_elim(+e: S.Edge, +xs: S.Es, +ys: S.Es, p: L.Tr(S.mem(e, S.append(xs, ys)))) -> Or(L.Tr(S.mem(e, xs)), L.Tr(S.mem(e, ys))):
  match xs:
    case S.ENil{}:
      Inr{p}
    case S.ECons{+h, +t}:
      L.or_elim(S.edge_eq(e, h), S.mem(e, S.append(t, ys)), p, Unit, Unit{},
        Or(L.Tr(S.mem(e, S.ECons{h, t})), L.Tr(S.mem(e, ys))),
        u => q => Inl{L.or_l(S.edge_eq(e, h), S.mem(e, t), q)},
        u => q => lift_or(e, h, t, ys, mem_append_elim(e, t, ys, q)))

# join_cases: a member of join_if(a, f, rest, hit) is the new edge (a, f), which
# needs `hit`, or a member of `rest`.
def join_cases(+x: S.Edge, +a: Nat, +f: Nat, +rest: S.Es, +hit: Bool, p: L.Tr(S.mem(x, S.join_if(a, f, rest, hit))), -P: Type, kh: L.Tr(hit) -> L.Tr(S.edge_eq(x, S.E{a, f})) -> P, kr: L.Tr(S.mem(x, rest)) -> P) -> P:
  match hit:
    case True{}:
      L.or_elim(S.edge_eq(x, S.E{a, f}), S.mem(x, rest), p, Unit, Unit{}, P,
        u => q => kh({==}, q),
        u => q => kr(q))
    case False{}:
      kr(p)

# Pre: an edge (a, d) made from (x, b) has a = x, and (b, d) is in the list.
def Pre(+a: Nat, +x: Nat, +b: Nat, +d: Nat, +es: S.Es) -> Type:
  {a == x : Nat} & L.Tr(S.mem(S.E{b, d}, es))

def head_mem(+b: Nat, +d: Nat, +c: Nat, +f: Nat, +t: S.Es, hbc: L.Tr(S.neq(b, c)), hdf: L.Tr(S.neq(d, f))) -> L.Tr(S.mem(S.E{b, d}, S.ECons{S.E{c, f}, t})):
  e = L.edge_eq_from(b, d, c, f, hbc, hdf)
  %e : L.Tr(S.mem(S.E{b, d}, S.ECons{_, t}))
  M.mem_head(S.E{b, d}, t)

def elim_head(+a: Nat, +x: Nat, +b: Nat, +c: Nat, +d: Nat, +f: Nat, +t: S.Es, hbc: L.Tr(S.neq(b, c)), heq: L.Tr(S.edge_eq(S.E{a, d}, S.E{x, f}))) -> Pre(a, x, b, d, S.ECons{S.E{c, f}, t}):
  L.and_elim(S.neq(a, x), S.neq(d, f), heq, L.Tr(S.neq(b, c)), hbc, Pre(a, x, b, d, S.ECons{S.E{c, f}, t}),
    hbc1 => hax => hdf => (L.neq_sound(a, x, hax), head_mem(b, d, c, f, t, hbc1, hdf)))

def lift_pre(+a: Nat, +x: Nat, +b: Nat, +d: Nat, +c: Nat, +f: Nat, +t: S.Es, r: Pre(a, x, b, d, t)) -> Pre(a, x, b, d, S.ECons{S.E{c, f}, t}):
  (l, m) = r
  (l, M.mem_tail(S.E{b, d}, S.E{c, f}, t, m))

# compose1_elim: a member of compose1((x, b), es) is (x, d) with (b, d) in es.
def compose1_elim(+a: Nat, +x: Nat, +b: Nat, +d: Nat, +es: S.Es, p: L.Tr(S.mem(S.E{a, d}, S.compose1(S.E{x, b}, es)))) -> Pre(a, x, b, d, es):
  match es:
    case S.ENil{}:
      Empty.absurd(Pre(a, x, b, d, S.ENil{}), L.false_ne_true(p))
    case S.ECons{S.E{+c, +f}, +t}:
      join_cases(S.E{a, d}, x, f, S.compose1(S.E{x, b}, t), S.neq(b, c), p,
        Pre(a, x, b, d, S.ECons{S.E{c, f}, t}),
        hbc => heq => elim_head(a, x, b, c, d, f, t, hbc, heq),
        q => lift_pre(a, x, b, d, c, f, t, compose1_elim(a, x, b, d, t, q)))

# Wit: a middle node b with (a, b) in xs and (b, c) in ys.
def Wit(+a: Nat, +c: Nat, +xs: S.Es, +ys: S.Es) -> Type:
  &b: Nat -> (L.Tr(S.mem(S.E{a, b}, xs)) & L.Tr(S.mem(S.E{b, c}, ys)))

def head_eq(+a: Nat, +x: Nat, +y: Nat, +t: S.Es, h: {a == x : Nat}) -> L.Tr(S.mem(S.E{a, y}, S.ECons{S.E{x, y}, t})):
  %h : L.Tr(S.mem(S.E{a, y}, S.ECons{S.E{_, y}, t}))
  M.mem_head(S.E{a, y}, t)

def wit_head(+a: Nat, +c: Nat, +x: Nat, +y: Nat, +t: S.Es, +ys: S.Es, r: Pre(a, x, y, c, ys)) -> Wit(a, c, S.ECons{S.E{x, y}, t}, ys):
  (hax, hm) = r
  (y, (head_eq(a, x, y, t, hax), hm))

def wit_tail(+a: Nat, +c: Nat, +x: Nat, +y: Nat, +t: S.Es, +ys: S.Es, w: Wit(a, c, t, ys)) -> Wit(a, c, S.ECons{S.E{x, y}, t}, ys):
  (+b, m) = w
  (m1, m2) = m
  (b, (M.mem_tail(S.E{a, b}, S.E{x, y}, t, m1), m2))

# compose_cases takes the recursive call as `rec`, so it never calls
# compose_elim itself: Bend has no mutual recursion.
def compose_cases(+a: Nat, +c: Nat, +x: Nat, +y: Nat, +t: S.Es, +ys: S.Es, r: Or(L.Tr(S.mem(S.E{a, c}, S.compose1(S.E{x, y}, ys))), L.Tr(S.mem(S.E{a, c}, S.compose(t, ys)))), rec: L.Tr(S.mem(S.E{a, c}, S.compose(t, ys))) -> Wit(a, c, t, ys)) -> Wit(a, c, S.ECons{S.E{x, y}, t}, ys):
  match r:
    case Inl{q}:
      wit_head(a, c, x, y, t, ys, compose1_elim(a, x, y, c, ys, q))
    case Inr{q}:
      wit_tail(a, c, x, y, t, ys, rec(q))

# compose_elim: a member of compose(xs, ys) is (a, c) through some middle b.
def compose_elim(+a: Nat, +c: Nat, +xs: S.Es, +ys: S.Es, p: L.Tr(S.mem(S.E{a, c}, S.compose(xs, ys)))) -> Wit(a, c, xs, ys):
  match xs:
    case S.ENil{}:
      Empty.absurd(Wit(a, c, S.ENil{}, ys), L.false_ne_true(p))
    case S.ECons{S.E{+x, +y}, +t}:
      compose_cases(a, c, x, y, t, ys,
        mem_append_elim(S.E{a, c}, S.compose1(S.E{x, y}, ys), S.compose(t, ys), p),
        q => compose_elim(a, c, t, ys, q))

def main() -> U32:
  1
