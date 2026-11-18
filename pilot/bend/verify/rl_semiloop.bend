# The semi-naive loop's proofs. The state is (old, delta), the graph
# `append(delta, old)`, and the invariant is `sat`: every firing among old
# triples, checked against old, is already in the graph.
#   semi_inv:          sat holds again for the next round's state;
#   iter_semi_closed:  when semi_fixed holds, the result is closed;
#   iter_semi_keeps:   the loop keeps what it started with;
#   iter_semi_least:   it stays inside any stable superset of the input.
# The pointwise steps become Bool `subset` tests through subset_pw.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_pairs.bend as RP
import ./rl_semi.bend as RS
import ./rl_loop.bend as RLp
import ./rl_sub.bend as Sb
import ./rl_pw.bend as RPw
import ./rl_fresh.bend as RFr
import ./rl_skip.bend as RK
import ./rl_sin.bend as RSi
import ./rl_least.bend as RLe

# ---- the invariant step

def sx(+cx: R.SemiCx) -> Bool:
  match cx:
    case R.SemiCx{+o, +d}:
      R.subset(R.pairs(o, o, o), R.append(d, o))

def sl0(+cx: R.SemiCx) -> R.Ts:
  match cx:
    case R.SemiCx{+o, +d}:
      R.derive(R.append(d, o))

def st(+cx: R.SemiCx) -> R.Ts:
  match cx:
    case R.SemiCx{+o, +d}:
      R.append(R.semi_delta(R.append(d, o), d), R.append(d, o))

def sg_fresh(+c: R.Tri, +o: R.Ts, +d: R.Ts, r: Or(L.Tr(R.mem(c, R.append(d, o))), L.Tr(R.mem(c, R.semi_delta(R.append(d, o), d))))) -> L.Tr(R.mem(c, R.append(R.semi_delta(R.append(d, o), d), R.append(d, o)))):
  match r:
    case Inl{a}:
      RM.mem_append_r(c, R.semi_delta(R.append(d, o), d), R.append(d, o), a)
    case Inr{b}:
      RM.mem_append_l(c, R.semi_delta(R.append(d, o), d), R.append(d, o), b)

def sg_cases(+c: R.Tri, +o: R.Ts, +d: R.Ts, r: Or(L.Tr(R.mem(c, R.append(d, o))), L.Tr(R.mem(c, R.derive_semi(d, R.append(d, o)))))) -> L.Tr(R.mem(c, R.append(R.semi_delta(R.append(d, o), d), R.append(d, o)))):
  match r:
    case Inl{a}:
      RM.mem_append_r(c, R.semi_delta(R.append(d, o), d), R.append(d, o), a)
    case Inr{q}:
      sg_fresh(c, o, d, RFr.fresh_complete(R.derive_semi(d, R.append(d, o)), R.append(d, o), R.TNil{}, c, q))

def sg(+cx: R.SemiCx, +c: R.Tri, e: L.Tr(sx(cx)), m: L.Tr(R.mem(c, sl0(cx)))) -> L.Tr(R.mem(c, st(cx))):
  match cx:
    case R.SemiCx{+o, +d}:
      sg_cases(c, o, d, RK.semi_skip(o, d, c, e, m))

# semi_inv: if every firing among old triples is in the graph, then every firing
# among the next round's old triples (this graph) is in the next graph.
def semi_inv(+old: R.Ts, +delta: R.Ts, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old)))) -> L.Tr(R.subset(R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)), R.append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old)))):
  RPw.subset_pw(~R.SemiCx, ~sx, ~sl0, ~st, ~sg, R.SemiCx{old, delta}, R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)),
    RS.dup(Bool, sx(R.SemiCx{old, delta}), True{}, sat),
    Sb.subset_refl(R.derive(R.append(delta, old))))

# ---- stop means closed

def is_nil_eq(+l: R.Ts, h: L.Tr(R.is_nil(l))) -> {l == R.TNil{} : R.Ts}:
  match l:
    case R.TNil{}:
      {==}
    case R.TCons{+x, +t}:
      Empty.absurd({R.TCons{x, t} == R.TNil{} : R.Ts}, L.false_ne_true(h))

# nil_absurd: nothing is a member of a list known to be empty.
def nil_absurd(+l: R.Ts, +c: R.Tri, h: {l == R.TNil{} : R.Ts}) -> (L.Tr(R.mem(c, l)) -> Empty):
  %Equal.sym(R.Ts, l, R.TNil{}, h) : (L.Tr(R.mem(c, _)) -> Empty)
  p => L.false_ne_true(p)

def sc_fresh(+c: R.Tri, +old: R.Ts, +delta: R.Ts, stop: {R.semi_delta(R.append(delta, old), delta) == R.TNil{} : R.Ts}, r: Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.semi_delta(R.append(delta, old), delta))))) -> L.Tr(R.mem(c, R.append(delta, old))):
  match r:
    case Inl{x}:
      x
    case Inr{y}:
      Empty.absurd(L.Tr(R.mem(c, R.append(delta, old))), nil_absurd(R.semi_delta(R.append(delta, old), delta), c, stop)(y))

def sc_cases(+c: R.Tri, +old: R.Ts, +delta: R.Ts, stop: {R.semi_delta(R.append(delta, old), delta) == R.TNil{} : R.Ts}, r: Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old)))))) -> L.Tr(R.mem(c, R.append(delta, old))):
  match r:
    case Inl{x}:
      x
    case Inr{q}:
      sc_fresh(c, old, delta, stop, RFr.fresh_complete(R.derive_semi(delta, R.append(delta, old)), R.append(delta, old), R.TNil{}, c, q))

# semi_closed: with sat, and a round that adds nothing, the graph is closed.
def semi_closed(+old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, +c: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), stop: {R.semi_delta(R.append(delta, old), delta) == R.TNil{} : R.Ts}, ha: L.Tr(R.mem(a, R.append(delta, old))), hb: L.Tr(R.mem(b, R.append(delta, old))), hc: L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old))))) -> L.Tr(R.mem(c, R.append(delta, old))):
  sc_cases(c, old, delta, stop,
    RK.semi_skip(old, delta, c, sat, RP.pairs_has(a, b, c, R.append(delta, old), R.append(delta, old), R.append(delta, old), ha, (hb, hc))))

# ---- the loop

# iter_semi_keeps: the loop keeps every triple it started with.
def iter_semi_keeps(+n: Nat, +old: R.Ts, +delta: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.append(delta, old)))) -> L.Tr(R.mem(c, R.iter_semi(n, old, delta))):
  match n:
    case 0n:
      p
    case 1n+q:
      iter_semi_keeps(q, R.append(delta, old), R.semi_delta(R.append(delta, old), delta), c,
        RM.mem_append_r(c, R.semi_delta(R.append(delta, old), delta), R.append(delta, old), p))

# iter_semi_closed: when semi_fixed holds, the result of n rounds is closed.
def iter_semi_closed(+n: Nat, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, +c: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), fixed: L.Tr(R.semi_fixed(n, old, delta)), ha: L.Tr(R.mem(a, R.iter_semi(n, old, delta))), hb: L.Tr(R.mem(b, R.iter_semi(n, old, delta))), hc: L.Tr(R.mem(c, R.fire(a, b, R.iter_semi(n, old, delta))))) -> L.Tr(R.mem(c, R.iter_semi(n, old, delta))):
  match n:
    case 0n:
      semi_closed(old, delta, a, b, c, sat, is_nil_eq(R.semi_delta(R.append(delta, old), delta), fixed), ha, hb, hc)
    case 1n+q:
      iter_semi_closed(q, R.append(delta, old), R.semi_delta(R.append(delta, old), delta), a, b, c, semi_inv(old, delta, sat), fixed, ha, hb, hc)

# ---- leastness: the loop stays inside any stable superset of its input

def ll_x(+cx: R.LoopCx) -> Bool:
  match cx:
    case R.LoopCx{+o, +d, +s}:
      S.and(R.subset(R.append(d, o), s), R.subset(R.step(s), s))

def ll_l0(+cx: R.LoopCx) -> R.Ts:
  match cx:
    case R.LoopCx{+o, +d, +s}:
      R.semi_delta(R.append(d, o), d)

def ll_t(+cx: R.LoopCx) -> R.Ts:
  match cx:
    case R.LoopCx{+o, +d, +s}:
      s

def ll_cases(+c: R.Tri, +o: R.Ts, +d: R.Ts, +s: R.Ts, hr: L.Tr(R.subset(R.append(d, o), s)), hst: L.Tr(R.subset(R.step(s), s)), r: Or(L.Tr(R.mem(c, R.derive_semi(d, R.append(d, o)))), L.Tr(R.mem(c, R.TNil{})))) -> L.Tr(R.mem(c, s)):
  match r:
    case Inl{q}:
      RLe.derive_in(c, R.append(d, o), s, hr, hst, RSi.semi_in_derive(c, d, o, q))
    case Inr{z}:
      Empty.absurd(L.Tr(R.mem(c, s)), L.false_ne_true(z))

def ll_g(+cx: R.LoopCx, +c: R.Tri, e: L.Tr(ll_x(cx)), m: L.Tr(R.mem(c, ll_l0(cx)))) -> L.Tr(R.mem(c, ll_t(cx))):
  match cx:
    case R.LoopCx{+o, +d, +s}:
      L.and_elim(R.subset(R.append(d, o), s), R.subset(R.step(s), s), e, Unit, Unit{}, L.Tr(R.mem(c, s)),
        u => hr => hst => ll_cases(c, o, d, s, hr, hst, RFr.fresh_sound(R.derive_semi(d, R.append(d, o)), R.append(d, o), R.TNil{}, c, m)))

# semi_least_step: if the graph and step(s) are inside s, so is the next graph.
def semi_least_step(+old: R.Ts, +delta: R.Ts, +s: R.Ts, t3: L.Tr(S.and(R.subset(R.append(delta, old), s), R.subset(R.step(s), s))) & (L.Tr(S.and(R.subset(R.append(delta, old), s), R.subset(R.step(s), s))) & L.Tr(S.and(R.subset(R.append(delta, old), s), R.subset(R.step(s), s))))) -> L.Tr(S.and(R.subset(R.append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old)), s), R.subset(R.step(s), s))):
  (e1, rest) = t3
  (e2, e3) = rest
  L.and_elim(R.subset(R.append(delta, old), s), R.subset(R.step(s), s), e2,
    L.Tr(R.subset(R.semi_delta(R.append(delta, old), delta), s)),
    RPw.subset_pw(~R.LoopCx, ~ll_x, ~ll_l0, ~ll_t, ~ll_g, R.LoopCx{old, delta, s}, R.semi_delta(R.append(delta, old), delta),
      RS.dup(Bool, ll_x(R.LoopCx{old, delta, s}), True{}, e1),
      Sb.subset_refl(R.semi_delta(R.append(delta, old), delta))),
    L.Tr(S.and(R.subset(R.append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old)), s), R.subset(R.step(s), s))),
    hd => hall => hst1 => L.and_elim(R.subset(R.append(delta, old), s), R.subset(R.step(s), s), e3,
      L.Tr(R.subset(R.append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old)), s)),
      Sb.subset_append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old), s, hd, hall),
      L.Tr(S.and(R.subset(R.append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old)), s), R.subset(R.step(s), s))),
      hz => hall2 => hstb => L.and_intro(R.subset(R.append(R.semi_delta(R.append(delta, old), delta), R.append(delta, old)), s), R.subset(R.step(s), s), hz, hstb)))

# iter_semi_least: n rounds from a graph inside a stable s stay inside s.
def iter_semi_least(+n: Nat, +old: R.Ts, +delta: R.Ts, +s: R.Ts, b: L.Tr(S.and(R.subset(R.append(delta, old), s), R.subset(R.step(s), s)))) -> L.Tr(R.subset(R.iter_semi(n, old, delta), s)):
  match n:
    case 0n:
      L.and_elim(R.subset(R.append(delta, old), s), R.subset(R.step(s), s), b, Unit, Unit{}, L.Tr(R.subset(R.append(delta, old), s)),
        u => hall => hst => hall)
    case 1n+q:
      iter_semi_least(q, R.append(delta, old), R.semi_delta(R.append(delta, old), delta), s,
        semi_least_step(old, delta, s, RPw.dup3(Bool, S.and(R.subset(R.append(delta, old), s), R.subset(R.step(s), s)), True{}, b)))

def main() -> U32:
  1
