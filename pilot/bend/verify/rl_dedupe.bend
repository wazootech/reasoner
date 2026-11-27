# Lemmas about insert and union in the six-rule model (from dedupe.bend).
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM

def insert_if_has(+hit: Bool, +e: R.Tri, +es: R.Ts, eq: {R.mem(e, es) == hit : Bool}) -> L.Tr(R.mem(e, R.insert_if(hit, e, es))):
  match hit:
    case True{}:
      eq
    case False{}:
      RM.mem_head(e, es)

# insert_has: the inserted edge is present afterwards.
def insert_has(+e: R.Tri, +es: R.Ts) -> L.Tr(R.mem(e, R.insert(e, es))):
  insert_if_has(R.mem(e, es), e, es, {==})

def insert_if_keeps(+hit: Bool, +x: R.Tri, +e: R.Tri, +es: R.Ts, p: L.Tr(R.mem(x, es))) -> L.Tr(R.mem(x, R.insert_if(hit, e, es))):
  match hit:
    case True{}:
      p
    case False{}:
      RM.mem_tail(x, e, es, p)

# insert_keeps: insert never loses an edge.
def insert_keeps(+x: R.Tri, +e: R.Tri, +es: R.Ts, p: L.Tr(R.mem(x, es))) -> L.Tr(R.mem(x, R.insert(e, es))):
  insert_if_keeps(R.mem(e, es), x, e, es, p)

def insert_if_elim(+hit: Bool, +x: R.Tri, +e: R.Tri, +es: R.Ts, p: L.Tr(R.mem(x, R.insert_if(hit, e, es)))) -> Or(L.Tr(R.mem(x, es)), L.Tr(R.tri_eq(x, e))):
  match hit:
    case True{}:
      Inl{p}
    case False{}:
      L.or_elim(R.tri_eq(x, e), R.mem(x, es), p, Unit, Unit{},
        Or(L.Tr(R.mem(x, es)), L.Tr(R.tri_eq(x, e))),
        u => q => Inr{q},
        u => q => Inl{q})

# insert_elim: a member of insert(e, es) is e or a member of es.
def insert_elim(+x: R.Tri, +e: R.Tri, +es: R.Ts, p: L.Tr(R.mem(x, R.insert(e, es)))) -> Or(L.Tr(R.mem(x, es)), L.Tr(R.tri_eq(x, e))):
  insert_if_elim(R.mem(e, es), x, e, es, p)

# union_keeps: union never loses a base edge.
def union_keeps(+x: R.Tri, +xs: R.Ts, +base: R.Ts, p: L.Tr(R.mem(x, base))) -> L.Tr(R.mem(x, R.union(xs, base))):
  match xs:
    case R.TNil{}:
      p
    case R.TCons{+h, +t}:
      union_keeps(x, t, R.insert(h, base), insert_keeps(x, h, base, p))

# union_has: union keeps every edge of xs.
def union_has(+x: R.Tri, +xs: R.Ts, +base: R.Ts, p: L.Tr(R.mem(x, xs))) -> L.Tr(R.mem(x, R.union(xs, base))):
  match xs:
    case R.TNil{}:
      Empty.absurd(L.Tr(R.mem(x, R.union(R.TNil{}, base))), L.false_ne_true(p))
    case R.TCons{+h, +t}:
      L.or_elim(R.tri_eq(x, h), R.mem(x, t), p, Unit, Unit{},
        L.Tr(R.mem(x, R.union(t, R.insert(h, base)))),
        u => q => union_keeps(x, t, R.insert(h, base), RM.mem_tri_eq(x, h, R.insert(h, base), q, insert_has(h, base))),
        u => q => union_has(x, t, R.insert(h, base), q))

def insert_cases(+x: R.Tri, +h: R.Tri, +t: R.Ts, +base: R.Ts, r: Or(L.Tr(R.mem(x, base)), L.Tr(R.tri_eq(x, h)))) -> Or(L.Tr(R.mem(x, R.TCons{h, t})), L.Tr(R.mem(x, base))):
  match r:
    case Inl{a}:
      Inr{a}
    case Inr{b}:
      Inl{L.or_l(R.tri_eq(x, h), R.mem(x, t), b)}

def union_cases(+x: R.Tri, +h: R.Tri, +t: R.Ts, +base: R.Ts, r: Or(L.Tr(R.mem(x, t)), L.Tr(R.mem(x, R.insert(h, base))))) -> Or(L.Tr(R.mem(x, R.TCons{h, t})), L.Tr(R.mem(x, base))):
  match r:
    case Inl{q}:
      Inl{L.or_r(R.tri_eq(x, h), R.mem(x, t), q)}
    case Inr{q}:
      insert_cases(x, h, t, base, insert_elim(x, h, base, q))

# union_elim: a member of union(xs, base) is a member of xs or of base.
def union_elim(+x: R.Tri, +xs: R.Ts, +base: R.Ts, p: L.Tr(R.mem(x, R.union(xs, base)))) -> Or(L.Tr(R.mem(x, xs)), L.Tr(R.mem(x, base))):
  match xs:
    case R.TNil{}:
      Inr{p}
    case R.TCons{+h, +t}:
      union_cases(x, h, t, base, union_elim(x, t, R.insert(h, base), p))

def main() -> U32:
  1
