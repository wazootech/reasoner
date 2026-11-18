# Least closure for the naive loop: if S contains the input and is stable (a
# round adds nothing to it), then every round of iter stays inside S. So when the
# loop's stop test passes, its result is the smallest closed superset of the
# input. The pointwise step is turned into a Bool `subset` by subset_pw.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_dedupe.bend as RD
import ./rl_loop.bend as RLp
import ./rl_pairs.bend as RP
import ./rl_semi.bend as RS
import ./rl_sub.bend as Sb
import ./rl_pw.bend as RPw
import ./rl_fmono.bend as RF

# dstep: a, b in r (so in s) and c in fire(a, b, r): c is in s, since s is stable.
def dstep(+a: R.Tri, +b: R.Tri, +c: R.Tri, +r: R.Ts, +s: R.Ts, ma: L.Tr(R.mem(a, r)), mb: L.Tr(R.mem(b, r)), hf: L.Tr(R.mem(c, R.fire(a, b, r))), t3: L.Tr(R.subset(r, s)) & (L.Tr(R.subset(r, s)) & L.Tr(R.subset(r, s))), hst: L.Tr(R.subset(R.step(s), s))) -> L.Tr(R.mem(c, s)):
  (h1, rest) = t3
  (h2, h3) = rest
  RLp.sub_elim(c, R.step(s), s, hst,
    RD.union_has(c, R.derive(s), s,
      RP.pairs_has(a, b, c, s, s, s, RLp.sub_elim(a, r, s, h1, ma), (RLp.sub_elim(b, r, s, h2, mb), RF.fire_mono(a, b, c, r, s, h3, hf)))))

def derive_conv(+c: R.Tri, +r: R.Ts, +s: R.Ts, hr: L.Tr(R.subset(r, s)), hst: L.Tr(R.subset(R.step(s), s)), w: RP.WA(c, r, r, r)) -> L.Tr(R.mem(c, s)):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  dstep(a, b, c, r, s, ma, mb, hf, RPw.dup3(Bool, R.subset(r, s), True{}, hr), hst)

# derive_in: what a round derives from a graph inside a stable s is inside s.
def derive_in(+c: R.Tri, +r: R.Ts, +s: R.Ts, hr: L.Tr(R.subset(r, s)), hst: L.Tr(R.subset(R.step(s), s)), q: L.Tr(R.mem(c, R.derive(r)))) -> L.Tr(R.mem(c, s)):
  derive_conv(c, r, s, hr, hst, RP.pairs_elim(c, r, r, r, q))

def step_cases(+c: R.Tri, +r: R.Ts, +s: R.Ts, hr: L.Tr(R.subset(r, s)), hst: L.Tr(R.subset(R.step(s), s)), o: Or(L.Tr(R.mem(c, R.derive(r))), L.Tr(R.mem(c, r)))) -> L.Tr(R.mem(c, s)):
  match o:
    case Inl{q}:
      derive_in(c, r, s, hr, hst, q)
    case Inr{q}:
      RLp.sub_elim(c, r, s, hr, q)

def step_in(+c: R.Tri, +r: R.Ts, +s: R.Ts, hr: L.Tr(R.subset(r, s)), hst: L.Tr(R.subset(R.step(s), s)), m: L.Tr(R.mem(c, R.step(r)))) -> L.Tr(R.mem(c, s)):
  step_cases(c, r, s, hr, hst, RD.union_elim(c, R.derive(r), r, m))

# The closed lemmas subset_pw is instantiated with.
def lc_x(+cx: R.LeastCx) -> Bool:
  match cx:
    case R.LeastCx{+r, +s}:
      S.and(R.subset(r, s), R.subset(R.step(s), s))

def lc_l0(+cx: R.LeastCx) -> R.Ts:
  match cx:
    case R.LeastCx{+r, +s}:
      R.step(r)

def lc_t(+cx: R.LeastCx) -> R.Ts:
  match cx:
    case R.LeastCx{+r, +s}:
      s

def lc_g(+cx: R.LeastCx, +c: R.Tri, e: L.Tr(lc_x(cx)), m: L.Tr(R.mem(c, lc_l0(cx)))) -> L.Tr(R.mem(c, lc_t(cx))):
  match cx:
    case R.LeastCx{+r, +s}:
      L.and_elim(R.subset(r, s), R.subset(R.step(s), s), e, Unit, Unit{}, L.Tr(R.mem(c, s)),
        u => hr => hst => step_in(c, r, s, hr, hst, m))

# step_sub: a round from a graph inside a stable s stays inside s.
def step_sub(+r: R.Ts, +s: R.Ts, hr: L.Tr(R.subset(r, s)), hst: L.Tr(R.subset(R.step(s), s))) -> L.Tr(R.subset(R.step(r), s)):
  RPw.subset_pw(~R.LeastCx, ~lc_x, ~lc_l0, ~lc_t, ~lc_g, R.LeastCx{r, s}, R.step(r),
    RS.dup(Bool, lc_x(R.LeastCx{r, s}), True{}, L.and_intro(R.subset(r, s), R.subset(R.step(s), s), hr, hst)),
    Sb.subset_refl(R.step(r)))

# iter_least: every round of iter stays inside a stable superset of the input.
def iter_least(+n: Nat, +ts: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(ts, s)), d: L.Tr(R.subset(R.step(s), s)) & L.Tr(R.subset(R.step(s), s))) -> L.Tr(R.subset(R.iter(n, ts), s)):
  match n:
    case 0n:
      hsub
    case 1n+p:
      (da, db) = d
      step_sub(R.iter(p, ts), s, iter_least(p, ts, s, hsub, RS.dup(Bool, R.subset(R.step(s), s), True{}, da)), db)

def main() -> U32:
  1
