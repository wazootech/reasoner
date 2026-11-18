# The old-pairs case of the semi-naive skip law. Given a conclusion c of two
# triples a, b that are both old, either the same conclusion fires against the
# old graph alone (rules 1-6 do not read the graph; prp-trp does when its
# transitive declaration is old), or the declaration is new, which derive_semi
# seeds with has_new_trans. Generated: the seven rules share one pattern.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_guard.bend as RG
import ./rl_pairs.bend as RP
import ./rl_rules.bend as RR
import ./rl_loop.bend as RLp

# dup turns one equality proof into two, by rewriting both copies at once.
def dup(-A: Type, -x: A, -y: A, h: {x == y : A}) -> {x == y : A} & {x == y : A}:
  %h : ({x == _ : A} & {x == _ : A})
  ({==}, {==})

def hnt_head(+s0: Nat, +p0: Nat, +o0: Nat, +t: R.Ts, +p: Nat, q: L.Tr(R.tri_eq(R.T{p, 0n, 5n}, R.T{s0, p0, o0}))) -> L.Tr(R.has_new_trans(R.TCons{R.T{s0, p0, o0}, t})):
  L.and_elim(S.and(S.neq(p, s0), S.neq(0n, p0)), S.neq(5n, o0), q, Unit, Unit{}, L.Tr(R.has_new_trans(R.TCons{R.T{s0, p0, o0}, t})),
    u => hab => hc => L.and_elim(S.neq(p, s0), S.neq(0n, p0), hab, L.Tr(S.neq(5n, o0)), hc, L.Tr(R.has_new_trans(R.TCons{R.T{s0, p0, o0}, t})),
      hc1 => hs => hp => L.or_l(S.and(S.neq(0n, p0), S.neq(5n, o0)), R.has_new_trans(t), L.and_intro(S.neq(0n, p0), S.neq(5n, o0), hp, hc1))))

# has_new_trans_of_mem: a declaration in delta is seen by has_new_trans.
def has_new_trans_of_mem(+delta: R.Ts, +p: Nat, h: L.Tr(R.mem(R.T{p, 0n, 5n}, delta))) -> L.Tr(R.has_new_trans(delta)):
  match delta:
    case R.TNil{}:
      Empty.absurd(L.Tr(R.has_new_trans(R.TNil{})), L.false_ne_true(h))
    case R.TCons{R.T{+s0, +p0, +o0}, +t}:
      L.or_elim(R.tri_eq(R.T{p, 0n, 5n}, R.T{s0, p0, o0}), R.mem(R.T{p, 0n, 5n}, t), h, Unit, Unit{},
        L.Tr(R.has_new_trans(R.TCons{R.T{s0, p0, o0}, t})),
        u => q => hnt_head(s0, p0, o0, t, p, q),
        u => q => L.or_r(S.and(S.neq(0n, p0), S.neq(5n, o0)), R.has_new_trans(t), has_new_trans_of_mem(t, p, q)))

def Res(+a: R.Tri, +b: R.Tri, +c: R.Tri, +old: R.Ts, +delta: R.Ts) -> Type:
  Or(L.Tr(R.mem(c, R.fire(a, b, old))), (L.Tr(R.has_new_trans(delta)) & L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old))))))

def in_old1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +old: R.Ts, +c: R.Tri, i: RR.In1(a, b, ts, c)) -> L.Tr(R.mem(c, R.fire(a, b, old))):
  (hit, ceq) = i
  %Equal.sym(R.Tri, c, R.out1(a, b), ceq) : L.Tr(R.mem(_, R.fire(a, b, old)))
  RR.has1(a, b, old, hit)

def in_old2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +old: R.Ts, +c: R.Tri, i: RR.In2(a, b, ts, c)) -> L.Tr(R.mem(c, R.fire(a, b, old))):
  (hit, ceq) = i
  %Equal.sym(R.Tri, c, R.out2(a, b), ceq) : L.Tr(R.mem(_, R.fire(a, b, old)))
  RR.has2(a, b, old, hit)

def in_old3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +old: R.Ts, +c: R.Tri, i: RR.In3(a, b, ts, c)) -> L.Tr(R.mem(c, R.fire(a, b, old))):
  (hit, ceq) = i
  %Equal.sym(R.Tri, c, R.out3(a, b), ceq) : L.Tr(R.mem(_, R.fire(a, b, old)))
  RR.has3(a, b, old, hit)

def in_old4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +old: R.Ts, +c: R.Tri, i: RR.In4(a, b, ts, c)) -> L.Tr(R.mem(c, R.fire(a, b, old))):
  (hit, ceq) = i
  %Equal.sym(R.Tri, c, R.out4(a, b), ceq) : L.Tr(R.mem(_, R.fire(a, b, old)))
  RR.has4(a, b, old, hit)

def in_old5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +old: R.Ts, +c: R.Tri, i: RR.In5(a, b, ts, c)) -> L.Tr(R.mem(c, R.fire(a, b, old))):
  (hit, ceq) = i
  %Equal.sym(R.Tri, c, R.out5(a, b), ceq) : L.Tr(R.mem(_, R.fire(a, b, old)))
  RR.has5(a, b, old, hit)

def in_old6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +old: R.Ts, +c: R.Tri, i: RR.In6(a, b, ts, c)) -> L.Tr(R.mem(c, R.fire(a, b, old))):
  (hit, ceq) = i
  %Equal.sym(R.Tri, c, R.out6(a, b), ceq) : L.Tr(R.mem(_, R.fire(a, b, old)))
  RR.has6(a, b, old, hit)

# mc7: with prp-trp's guard rebuilt against ts, its conclusion is in fire(a, b, ts).
def mc7(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +ts: R.Ts, hab: L.Tr(S.and(S.neq(pa, pb), S.neq(oa, sb))), hm: L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)), ceq: {c == R.out7(R.T{sa, pa, oa}, R.T{sb, pb, ob}) : R.Tri}) -> L.Tr(R.mem(c, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts))):
  %Equal.sym(R.Tri, c, R.out7(R.T{sa, pa, oa}, R.T{sb, pb, ob}), ceq) : L.Tr(R.mem(_, R.fire(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts)))
  RR.has7(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, L.and_intro(S.and(S.neq(pa, pb), S.neq(oa, sb)), R.mem(R.T{pa, 0n, 5n}, ts), hab, hm))

def oc7c(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, hab: L.Tr(S.and(S.neq(pa, pb), S.neq(oa, sb))), ceq: {c == R.out7(R.T{sa, pa, oa}, R.T{sb, pb, ob}) : R.Tri}, d: L.Tr(R.mem(R.T{pa, 0n, 5n}, delta)) & L.Tr(R.mem(R.T{pa, 0n, 5n}, delta))) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  (md1, md2) = d
  Inr{(has_new_trans_of_mem(delta, pa, md1), mc7(sa, pa, oa, sb, pb, ob, c, R.append(delta, old), hab, RM.mem_append_l(R.T{pa, 0n, 5n}, delta, old, md2), ceq))}

def oc7b(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, hab: L.Tr(S.and(S.neq(pa, pb), S.neq(oa, sb))), ceq: {c == R.out7(R.T{sa, pa, oa}, R.T{sb, pb, ob}) : R.Tri}, r: Or(L.Tr(R.mem(R.T{pa, 0n, 5n}, delta)), L.Tr(R.mem(R.T{pa, 0n, 5n}, old)))) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match r:
    case Inl{md}:
      oc7c(sa, pa, oa, sb, pb, ob, c, old, delta, hab, ceq, dup(Bool, R.mem(R.T{pa, 0n, 5n}, delta), True{}, md))
    case Inr{mo}:
      Inl{mc7(sa, pa, oa, sb, pb, ob, c, old, hab, mo, ceq)}

def oc7(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, i: RR.In7(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  (hit, ceq) = i
  L.and_elim(S.and(S.neq(pa, pb), S.neq(oa, sb)), R.mem(R.T{pa, 0n, 5n}, R.append(delta, old)), hit, {c == R.out7(R.T{sa, pa, oa}, R.T{sb, pb, ob}) : R.Tri}, ceq, Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta),
    ceq1 => hab => hm => oc7b(sa, pa, oa, sb, pb, ob, c, old, delta, hab, ceq1, RM.mem_append_elim(R.T{pa, 0n, 5n}, delta, old, hm)))

def oc6(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, s: RR.Sum6(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match s:
    case Inl{x}:
      Inl{in_old6(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), old, c, x)}
    case Inr{y}:
      oc7(sa, pa, oa, sb, pb, ob, c, old, delta, y)

def oc5(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, s: RR.Sum5(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match s:
    case Inl{x}:
      Inl{in_old5(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), old, c, x)}
    case Inr{y}:
      oc6(sa, pa, oa, sb, pb, ob, c, old, delta, y)

def oc4(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, s: RR.Sum4(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match s:
    case Inl{x}:
      Inl{in_old4(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), old, c, x)}
    case Inr{y}:
      oc5(sa, pa, oa, sb, pb, ob, c, old, delta, y)

def oc3(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, s: RR.Sum3(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match s:
    case Inl{x}:
      Inl{in_old3(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), old, c, x)}
    case Inr{y}:
      oc4(sa, pa, oa, sb, pb, ob, c, old, delta, y)

def oc2(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, s: RR.Sum2(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match s:
    case Inl{x}:
      Inl{in_old2(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), old, c, x)}
    case Inr{y}:
      oc3(sa, pa, oa, sb, pb, ob, c, old, delta, y)

def oc1(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +c: R.Tri, +old: R.Ts, +delta: R.Ts, s: RR.Sum1(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c)) -> Res(R.T{sa, pa, oa}, R.T{sb, pb, ob}, c, old, delta):
  match s:
    case Inl{x}:
      Inl{in_old1(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), old, c, x)}
    case Inr{y}:
      oc2(sa, pa, oa, sb, pb, ob, c, old, delta, y)

def semi_old3(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, ao: L.Tr(R.mem(a, old)), bo: L.Tr(R.mem(b, old)), pr: L.Tr(R.has_new_trans(delta)) & L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old))))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  (htn, mc) = pr
  Inr{RM.mem_append_r(c, R.pairs(delta, R.append(delta, old), R.append(delta, old)), R.append(R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)))),
    RM.mem_append_r(c, R.pairs(R.append(delta, old), delta, R.append(delta, old)), R.guard(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old))),
      RG.guard_has(R.has_new_trans(delta), R.pairs(R.append(delta, old), R.append(delta, old), R.append(delta, old)), c, htn,
        RP.pairs_has(a, b, c, R.append(delta, old), R.append(delta, old), R.append(delta, old), RM.mem_append_r(a, delta, old, ao), (RM.mem_append_r(b, delta, old, bo), mc)))))}

def semi_old2(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), ao: L.Tr(R.mem(a, old)), bo: L.Tr(R.mem(b, old)), r: Res(a, b, c, old, delta)) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  match r:
    case Inl{q}:
      Inl{RLp.sub_elim(c, R.pairs(old, old, old), R.append(delta, old), sat, RP.pairs_has(a, b, c, old, old, old, ao, (bo, q)))}
    case Inr{pr}:
      semi_old3(c, old, delta, a, b, ao, bo, pr)

# semi_old: both premises are old.
def semi_old(+c: R.Tri, +old: R.Ts, +delta: R.Ts, +a: R.Tri, +b: R.Tri, sat: L.Tr(R.subset(R.pairs(old, old, old), R.append(delta, old))), hf: L.Tr(R.mem(c, R.fire(a, b, R.append(delta, old)))), ao: L.Tr(R.mem(a, old)), bo: L.Tr(R.mem(b, old))) -> Or(L.Tr(R.mem(c, R.append(delta, old))), L.Tr(R.mem(c, R.derive_semi(delta, R.append(delta, old))))):
  match a b:
    case R.T{+sa, +pa, +oa} R.T{+sb, +pb, +ob}:
      semi_old2(c, old, delta, R.T{sa, pa, oa}, R.T{sb, pb, ob}, sat, ao, bo,
        oc1(sa, pa, oa, sb, pb, ob, c, old, delta, RR.fire_cases(R.T{sa, pa, oa}, R.T{sb, pb, ob}, R.append(delta, old), c, hf)))

def main() -> U32:
  1
