# Lemmas about `insert` and `union`, the dedupe that keeps `step`'s lists free of
# duplicates. Each lemma on `insert` is stated for `insert_if` with the test as
# a parameter, since Bend cannot match on the computed `mem(e, es)`.
import Base
import ./sco.bend as S
import ./logic.bend as L
import ./mem.bend as M

def insert_if_has(+hit: Bool, +e: S.Edge, +es: S.Es, eq: {S.mem(e, es) == hit : Bool}) -> L.Tr(S.mem(e, S.insert_if(hit, e, es))):
  match hit:
    case True{}:
      eq
    case False{}:
      M.mem_head(e, es)

# insert_has: the inserted edge is present afterwards.
def insert_has(+e: S.Edge, +es: S.Es) -> L.Tr(S.mem(e, S.insert(e, es))):
  insert_if_has(S.mem(e, es), e, es, {==})

def insert_if_keeps(+hit: Bool, +x: S.Edge, +e: S.Edge, +es: S.Es, p: L.Tr(S.mem(x, es))) -> L.Tr(S.mem(x, S.insert_if(hit, e, es))):
  match hit:
    case True{}:
      p
    case False{}:
      M.mem_tail(x, e, es, p)

# insert_keeps: insert never loses an edge.
def insert_keeps(+x: S.Edge, +e: S.Edge, +es: S.Es, p: L.Tr(S.mem(x, es))) -> L.Tr(S.mem(x, S.insert(e, es))):
  insert_if_keeps(S.mem(e, es), x, e, es, p)

def insert_if_elim(+hit: Bool, +x: S.Edge, +e: S.Edge, +es: S.Es, p: L.Tr(S.mem(x, S.insert_if(hit, e, es)))) -> Or(L.Tr(S.mem(x, es)), L.Tr(S.edge_eq(x, e))):
  match hit:
    case True{}:
      Inl{p}
    case False{}:
      L.or_elim(S.edge_eq(x, e), S.mem(x, es), p, Unit, Unit{},
        Or(L.Tr(S.mem(x, es)), L.Tr(S.edge_eq(x, e))),
        u => q => Inr{q},
        u => q => Inl{q})

# insert_elim: a member of insert(e, es) is e or a member of es.
def insert_elim(+x: S.Edge, +e: S.Edge, +es: S.Es, p: L.Tr(S.mem(x, S.insert(e, es)))) -> Or(L.Tr(S.mem(x, es)), L.Tr(S.edge_eq(x, e))):
  insert_if_elim(S.mem(e, es), x, e, es, p)

# union_keeps: union never loses a base edge.
def union_keeps(+x: S.Edge, +xs: S.Es, +base: S.Es, p: L.Tr(S.mem(x, base))) -> L.Tr(S.mem(x, S.union(xs, base))):
  match xs:
    case S.ENil{}:
      p
    case S.ECons{+h, +t}:
      union_keeps(x, t, S.insert(h, base), insert_keeps(x, h, base, p))

# union_has: union keeps every edge of xs.
def union_has(+x: S.Edge, +xs: S.Es, +base: S.Es, p: L.Tr(S.mem(x, xs))) -> L.Tr(S.mem(x, S.union(xs, base))):
  match xs:
    case S.ENil{}:
      Empty.absurd(L.Tr(S.mem(x, S.union(S.ENil{}, base))), L.false_ne_true(p))
    case S.ECons{+h, +t}:
      L.or_elim(S.edge_eq(x, h), S.mem(x, t), p, Unit, Unit{},
        L.Tr(S.mem(x, S.union(t, S.insert(h, base)))),
        u => q => union_keeps(x, t, S.insert(h, base), M.mem_edge_eq(x, h, S.insert(h, base), q, insert_has(h, base))),
        u => q => union_has(x, t, S.insert(h, base), q))

def insert_cases(+x: S.Edge, +h: S.Edge, +t: S.Es, +base: S.Es, r: Or(L.Tr(S.mem(x, base)), L.Tr(S.edge_eq(x, h)))) -> Or(L.Tr(S.mem(x, S.ECons{h, t})), L.Tr(S.mem(x, base))):
  match r:
    case Inl{a}:
      Inr{a}
    case Inr{b}:
      Inl{L.or_l(S.edge_eq(x, h), S.mem(x, t), b)}

def union_cases(+x: S.Edge, +h: S.Edge, +t: S.Es, +base: S.Es, r: Or(L.Tr(S.mem(x, t)), L.Tr(S.mem(x, S.insert(h, base))))) -> Or(L.Tr(S.mem(x, S.ECons{h, t})), L.Tr(S.mem(x, base))):
  match r:
    case Inl{q}:
      Inl{L.or_r(S.edge_eq(x, h), S.mem(x, t), q)}
    case Inr{q}:
      insert_cases(x, h, t, base, insert_elim(x, h, base, q))

# union_elim: a member of union(xs, base) is a member of xs or of base.
def union_elim(+x: S.Edge, +xs: S.Es, +base: S.Es, p: L.Tr(S.mem(x, S.union(xs, base)))) -> Or(L.Tr(S.mem(x, xs)), L.Tr(S.mem(x, base))):
  match xs:
    case S.ENil{}:
      Inr{p}
    case S.ECons{+h, +t}:
      union_cases(x, h, t, base, union_elim(x, t, S.insert(h, base), p))

def main() -> U32:
  1
