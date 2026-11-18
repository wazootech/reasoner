# The six-rule model: the code that RL_LAWS.bend is about. A triple is three
# `Nat` ids; the vocabulary ids are fixed as in encode.ts (type 0, subClassOf 1,
# domain 2, range 3, inverseOf 4, TransitiveProperty 5). A graph is a list with
# no duplicates; the laws are about membership, so the list is a set.
#
# `fire(a, b, ts)` is every conclusion of the rules whose two premises are a and
# b: cax-sco, scm-sco, prp-dom, prp-rng, prp-inv1, prp-inv2, prp-trp, in that
# order. Each rule K is `hit_K` (do the premises match) and `out_K` (the
# conclusion). prp-trp has a third premise, `(p type TransitiveProperty)`,
# looked up in `ts`.
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

# cax-sco: (c1 subClassOf c2), (x type c1) gives (x type c2)
def hit1(+a: Tri, +b: Tri) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.and(S.neq(pa, 1n), S.neq(pb, 0n)), S.neq(ob, sa))

def out1(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{sb, 0n, oa}

# scm-sco: (c1 subClassOf c2), (c2 subClassOf c3) gives (c1 subClassOf c3)
def hit2(+a: Tri, +b: Tri) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.and(S.neq(pa, 1n), S.neq(pb, 1n)), S.neq(sb, oa))

def out2(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{sa, 1n, ob}

# prp-dom: (p domain c), (x p y) gives (x type c)
def hit3(+a: Tri, +b: Tri) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.neq(pa, 2n), S.neq(pb, sa))

def out3(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{sb, 0n, oa}

# prp-rng: (p range c), (x p y) gives (y type c)
def hit4(+a: Tri, +b: Tri) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.neq(pa, 3n), S.neq(pb, sa))

def out4(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{ob, 0n, oa}

# prp-inv1: (p1 inverseOf p2), (x p1 y) gives (y p2 x)
def hit5(+a: Tri, +b: Tri) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.neq(pa, 4n), S.neq(pb, sa))

def out5(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{ob, oa, sb}

# prp-inv2: (p1 inverseOf p2), (x p2 y) gives (y p1 x)
def hit6(+a: Tri, +b: Tri) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.neq(pa, 4n), S.neq(pb, oa))

def out6(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{ob, sa, sb}

# prp-trp: (p type TransitiveProperty), (x p y), (y p z) gives (x p z)
def hit7(+a: Tri, +b: Tri, +ts: Ts) -> Bool:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      S.and(S.and(S.neq(pa, pb), S.neq(oa, sb)), mem(T{pa, 0n, 5n}, ts))

def out7(+a: Tri, +b: Tri) -> Tri:
  match a b:
    case T{+sa, +pa, +oa} T{+sb, +pb, +ob}:
      T{sa, pa, ob}

# fire7 is the last rule; each fireK adds rule K in front of fire(K+1), so a
# proof can name the tail of the list.
def fire7(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  guard(hit7(a, b, ts), one(out7(a, b)))

def fire6(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  append(guard(hit6(a, b), one(out6(a, b))), fire7(a, b, ts))

def fire5(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  append(guard(hit5(a, b), one(out5(a, b))), fire6(a, b, ts))

def fire4(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  append(guard(hit4(a, b), one(out4(a, b))), fire5(a, b, ts))

def fire3(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  append(guard(hit3(a, b), one(out3(a, b))), fire4(a, b, ts))

def fire2(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  append(guard(hit2(a, b), one(out2(a, b))), fire3(a, b, ts))

def fire1(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  append(guard(hit1(a, b), one(out1(a, b))), fire2(a, b, ts))

# fire is every conclusion of the seven rules for the pair (a, b).
def fire(+a: Tri, +b: Tri, +ts: Ts) -> Ts:
  fire1(a, b, ts)

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

# has_new_trans: does delta declare a transitive property, (p type
# TransitiveProperty)? Such a triple is the third premise of prp-trp, so it
# seeds a round of its own.
def has_new_trans(+delta: Ts) -> Bool:
  match delta:
    case TNil{}:
      False{}
    case TCons{T{+s, +p, +o}, +t}:
      S.or(S.and(S.neq(0n, p), S.neq(5n, o)), has_new_trans(t))

# derive_semi is what a semi-naive round fires. Only pairs with a new triple are
# joined: one from `delta` against everything in `all`, on either side. And
# when `delta` declares a transitive property, every pair is joined, since that
# declaration is prp-trp's third premise and the data triples may be old. Pairs
# of old triples are otherwise skipped; RL_LAWS.bend proves that loses nothing.
def derive_semi(+delta: Ts, +all: Ts) -> Ts:
  append(pairs(delta, all, all), append(pairs(all, delta, all), guard(has_new_trans(delta), pairs(all, all, all))))

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

# fresh_go collects the triples of xs that base lacks, each once: it inserts each
# triple into base as it goes, so a repeat in xs is already there.
def fresh_go(+xs: Ts, +base: Ts, +acc: Ts) -> Ts:
  match xs:
    case TNil{}:
      acc
    case TCons{+h, +t}:
      fresh_go(t, insert(h, base), insert_if(mem(h, base), h, acc))

# semi_delta is the triples a semi-naive round adds: what derive_semi fires that
# `all` lacks.
def semi_delta(+all: Ts, +delta: Ts) -> Ts:
  fresh_go(derive_semi(delta, all), all, TNil{})

# iter_semi runs n semi-naive rounds from `all` with `delta` new. TESTED, NOT
# PROVED at the loop level: RL_LAWS.bend proves a round's skip is safe
# (semi_skip_safe), not that the loop keeps the invariant that law needs.
def iter_semi(+n: Nat, +all: Ts, +delta: Ts) -> Ts:
  match n:
    case 0n:
      all
    case 1n+p:
      +d = semi_delta(all, delta)
      iter_semi(p, append(d, all), d)

def main() -> Ts:
  # (A sub B), (B sub C), (x type A) gives (A sub C), (x type B) and (x type C).
  g : Ts = TCons{T{10n, 1n, 11n}, TCons{T{11n, 1n, 12n}, TCons{T{20n, 0n, 10n}, TNil{}}}}
  iter(3n, g)
