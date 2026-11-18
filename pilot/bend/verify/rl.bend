# The six-rule model: the code that RL_LAWS.bend is about. A triple is three
# `Nat` ids; the vocabulary ids are fixed as in encode.ts (type 0, subClassOf 1,
# domain 2, range 3, inverseOf 4, TransitiveProperty 5). A graph is a list with
# no duplicates; the laws are about membership, so the list is a set.
#
# `fire(a, b, ts)` is every conclusion of the rules whose two premises are a and
# b, in this order: cax-sco, scm-sco, prp-dom, prp-rng, prp-inv1, prp-inv2,
# prp-trp. prp-trp has a third premise, `(p type TransitiveProperty)`, looked up
# in `ts`.
import Base
import ./sco.bend as S

type Tri is Data:
  T{s: Nat, p: Nat, o: Nat}

type Ts is Data:
  TNil{}
  TCons{h: Tri, t: Ts}

def tri_eq(+x: Tri, +y: Tri) -> Bool:
  match x y:
    case T{+a, +b, +c} T{+d, +e, +f}:
      S.and(S.and(S.neq(a, d), S.neq(b, e)), S.neq(c, f))

def mem(+e: Tri, +ts: Ts) -> Bool:
  match ts:
    case TNil{}:
      False{}
    case TCons{+h, +t}:
      S.or(tri_eq(e, h), mem(e, t))

def append(+xs: Ts, +ys: Ts) -> Ts:
  match xs:
    case TNil{}:
      ys
    case TCons{+h, +t}:
      TCons{h, append(t, ys)}

# insert_if adds e in front of ts unless `hit` says it is already there. It is
# its own def because Bend cannot match on a computed value.
def insert_if(+hit: Bool, +e: Tri, +ts: Ts) -> Ts:
  match hit:
    case True{}:
      ts
    case False{}:
      TCons{e, ts}

def insert(+e: Tri, +ts: Ts) -> Ts:
  insert_if(mem(e, ts), e, ts)

# union inserts every triple of xs into base, so base never gains a duplicate.
def union(+xs: Ts, +base: Ts) -> Ts:
  match xs:
    case TNil{}:
      base
    case TCons{+h, +t}:
      union(t, insert(h, base))

# guard keeps xs only when the rule's premises matched.
def guard(+hit: Bool, +xs: Ts) -> Ts:
  match hit:
    case True{}:
      xs
    case False{}:
      TNil{}

def one(+x: Tri) -> Ts:
  TCons{x, TNil{}}

def fire(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      r7 : Ts = guard(S.and(S.and(S.neq(pa, pb), S.neq(oa, sb)), mem(T{pa, 0n, 5n}, ts)), one(T{sa, pa, ob}))
      r6 : Ts = append(guard(S.and(S.neq(pa, 4n), S.neq(pb, oa)), one(T{ob, sa, sb})), r7)
      r5 : Ts = append(guard(S.and(S.neq(pa, 4n), S.neq(pb, sa)), one(T{ob, oa, sb})), r6)
      r4 : Ts = append(guard(S.and(S.neq(pa, 3n), S.neq(pb, sa)), one(T{ob, 0n, oa})), r5)
      r3 : Ts = append(guard(S.and(S.neq(pa, 2n), S.neq(pb, sa)), one(T{sb, 0n, oa})), r4)
      r2 : Ts = append(guard(S.and(S.and(S.neq(pa, 1n), S.neq(pb, 1n)), S.neq(sb, oa)), one(T{sa, 1n, ob})), r3)
      append(guard(S.and(S.and(S.neq(pa, 1n), S.neq(pb, 0n)), S.neq(ob, sa)), one(T{sb, 0n, oa})), r2)

def pairs1(+a: Tri, +ys: Ts, +ts: Ts) -> Ts:
  match ys:
    case TNil{}:
      TNil{}
    case TCons{+b, +t}:
      append(fire(a, b, ts), pairs1(a, t, ts))

# pairs is fire over every pair (x, y) of xs and ys.
def pairs(+xs: Ts, +ys: Ts, +ts: Ts) -> Ts:
  match xs:
    case TNil{}:
      TNil{}
    case TCons{+h, +t}:
      append(pairs1(h, ys, ts), pairs(t, ys, ts))

def derive(+ts: Ts) -> Ts:
  pairs(ts, ts, ts)

# step is one round: the graph plus every triple the rules derive that it lacks.
def step(+ts: Ts) -> Ts:
  union(derive(ts), ts)

# subset is the loop's stop test: every triple of xs is in ys.
def subset(+xs: Ts, +ys: Ts) -> Bool:
  match xs:
    case TNil{}:
      True{}
    case TCons{+h, +t}:
      S.and(mem(h, ys), subset(t, ys))

# iter runs n rounds. Whether n rounds are enough is not proved: the caller
# checks `subset(step(r), r)` on the result.
def iter(+n: Nat, +ts: Ts) -> Ts:
  match n:
    case 0n:
      ts
    case 1n+p:
      step(iter(p, ts))

def main() -> Ts:
  # (A sub B), (B sub C), (x type A) gives (A sub C), (x type B) and (x type C).
  g : Ts = TCons{T{10n, 1n, 11n}, TCons{T{11n, 1n, 12n}, TCons{T{20n, 0n, 10n}, TNil{}}}}
  iter(3n, g)
