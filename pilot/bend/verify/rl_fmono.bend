# fire is monotone in its graph argument: if r is a subset of s, a conclusion of
# fire(a, b, r) is a conclusion of fire(a, b, s). Rules 1-6 do not read the graph;
# prp-trp reads it only for its lookup premise, which moves from r to s.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_rules.bend as RR
import ./rl_semi.bend as RS
import ./rl_loop.bend as RLp

def fm7(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), i: RR.In7(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  (hit, ceq) = i
  L.and_elim(S.and(S.neq(pa, pb), S.neq(oa, sb)), R.mem(R.T{pa, 0n, 5n}, r), hit, {c == R.out7(R.T{sa, pa, oa}, R.T{sb, pb, ob}) : R.Tri}, ceq, L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))),
    ceq1 => hab => hm => RS.mc7(sa, pa, oa, sb, pb, ob, c, s, hab, RLp.sub_elim(R.T{pa, 0n, 5n}, r, s, hsub, hm), ceq1))

def fsum6(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), sm: RR.Sum6(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  match sm:
    case Inl{x}:
      RS.in_old6(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, s, c, x)
    case Inr{y}:
      fm7(sa, pa, oa, sb, pb, ob, c, r, s, hsub, y)

def fsum5(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), sm: RR.Sum5(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  match sm:
    case Inl{x}:
      RS.in_old5(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, s, c, x)
    case Inr{y}:
      fsum6(sa, pa, oa, sb, pb, ob, c, r, s, hsub, y)

def fsum4(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), sm: RR.Sum4(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  match sm:
    case Inl{x}:
      RS.in_old4(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, s, c, x)
    case Inr{y}:
      fsum5(sa, pa, oa, sb, pb, ob, c, r, s, hsub, y)

def fsum3(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), sm: RR.Sum3(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  match sm:
    case Inl{x}:
      RS.in_old3(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, s, c, x)
    case Inr{y}:
      fsum4(sa, pa, oa, sb, pb, ob, c, r, s, hsub, y)

def fsum2(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), sm: RR.Sum2(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  match sm:
    case Inl{x}:
      RS.in_old2(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, s, c, x)
    case Inr{y}:
      fsum3(sa, pa, oa, sb, pb, ob, c, r, s, hsub, y)

def fsum1(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), sm: RR.Sum1(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c)) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, s))):
  match sm:
    case Inl{x}:
      RS.in_old1(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, s, c, x)
    case Inr{y}:
      fsum2(sa, pa, oa, sb, pb, ob, c, r, s, hsub, y)

# fire_mono: a conclusion of fire(a, b, r) is one of fire(a, b, s) when r is in s.
def fire_mono(+a: R.Tri, +b: R.Tri, +c: R.Tri, +r: R.Ts, +s: R.Ts, hsub: L.Tr(R.subset(r, s)), hf: L.Tr(R.mem(c, R.fire(a, b, r)))) -> L.Tr(R.mem(c, R.fire(a, b, s))):
  match a b:
    case R.T{+sa, +pa, +oa} R.T{+sb, +pb, +ob}:
      fsum1(sa, pa, oa, sb, pb, ob, c, r, s, hsub, RR.fire_cases(R.T{sa, pa, oa}, R.T{sb, pb, ob}, r, c, hf))

def main() -> U32:
  1
