# Per-rule proofs, generated from one pattern for all seven rules: a rule's
# conclusion is in `fire` when its guard holds (has_K), and everything in `fire`
# came from one of the seven guards (fire_cases, rule_sound).
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_logic.bend as RL
import ./rl_mem.bend as RM
import ./rl_guard.bend as RG
import ./rl_spec.bend as Sp

def up1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire2(a, b, ts)))) -> L.Tr(R.mem(c, R.fire1(a, b, ts))):
  RM.mem_append_r(c, R.guard(R.hit1(a, b), R.one(R.out1(a, b))), R.fire2(a, b, ts), p)

def up2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire3(a, b, ts)))) -> L.Tr(R.mem(c, R.fire2(a, b, ts))):
  RM.mem_append_r(c, R.guard(R.hit2(a, b), R.one(R.out2(a, b))), R.fire3(a, b, ts), p)

def up3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire4(a, b, ts)))) -> L.Tr(R.mem(c, R.fire3(a, b, ts))):
  RM.mem_append_r(c, R.guard(R.hit3(a, b), R.one(R.out3(a, b))), R.fire4(a, b, ts), p)

def up4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire5(a, b, ts)))) -> L.Tr(R.mem(c, R.fire4(a, b, ts))):
  RM.mem_append_r(c, R.guard(R.hit4(a, b), R.one(R.out4(a, b))), R.fire5(a, b, ts), p)

def up5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire6(a, b, ts)))) -> L.Tr(R.mem(c, R.fire5(a, b, ts))):
  RM.mem_append_r(c, R.guard(R.hit5(a, b), R.one(R.out5(a, b))), R.fire6(a, b, ts), p)

def up6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire7(a, b, ts)))) -> L.Tr(R.mem(c, R.fire6(a, b, ts))):
  RM.mem_append_r(c, R.guard(R.hit6(a, b), R.one(R.out6(a, b))), R.fire7(a, b, ts), p)

def here1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit1(a, b))) -> L.Tr(R.mem(R.out1(a, b), R.fire1(a, b, ts))):
  RM.mem_append_l(R.out1(a, b), R.guard(R.hit1(a, b), R.one(R.out1(a, b))), R.fire2(a, b, ts), RG.guard_has(R.hit1(a, b), R.one(R.out1(a, b)), R.out1(a, b), h, RG.one_has(R.out1(a, b))))

# has1: cax-sco's conclusion is in fire when its guard holds.
def has1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit1(a, b))) -> L.Tr(R.mem(R.out1(a, b), R.fire(a, b, ts))):
  here1(a, b, ts, h)

def here2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit2(a, b))) -> L.Tr(R.mem(R.out2(a, b), R.fire2(a, b, ts))):
  RM.mem_append_l(R.out2(a, b), R.guard(R.hit2(a, b), R.one(R.out2(a, b))), R.fire3(a, b, ts), RG.guard_has(R.hit2(a, b), R.one(R.out2(a, b)), R.out2(a, b), h, RG.one_has(R.out2(a, b))))

# has2: scm-sco's conclusion is in fire when its guard holds.
def has2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit2(a, b))) -> L.Tr(R.mem(R.out2(a, b), R.fire(a, b, ts))):
  up1(a, b, ts, R.out2(a, b), here2(a, b, ts, h))

def here3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit3(a, b))) -> L.Tr(R.mem(R.out3(a, b), R.fire3(a, b, ts))):
  RM.mem_append_l(R.out3(a, b), R.guard(R.hit3(a, b), R.one(R.out3(a, b))), R.fire4(a, b, ts), RG.guard_has(R.hit3(a, b), R.one(R.out3(a, b)), R.out3(a, b), h, RG.one_has(R.out3(a, b))))

# has3: prp-dom's conclusion is in fire when its guard holds.
def has3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit3(a, b))) -> L.Tr(R.mem(R.out3(a, b), R.fire(a, b, ts))):
  up1(a, b, ts, R.out3(a, b), up2(a, b, ts, R.out3(a, b), here3(a, b, ts, h)))

def here4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit4(a, b))) -> L.Tr(R.mem(R.out4(a, b), R.fire4(a, b, ts))):
  RM.mem_append_l(R.out4(a, b), R.guard(R.hit4(a, b), R.one(R.out4(a, b))), R.fire5(a, b, ts), RG.guard_has(R.hit4(a, b), R.one(R.out4(a, b)), R.out4(a, b), h, RG.one_has(R.out4(a, b))))

# has4: prp-rng's conclusion is in fire when its guard holds.
def has4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit4(a, b))) -> L.Tr(R.mem(R.out4(a, b), R.fire(a, b, ts))):
  up1(a, b, ts, R.out4(a, b), up2(a, b, ts, R.out4(a, b), up3(a, b, ts, R.out4(a, b), here4(a, b, ts, h))))

def here5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit5(a, b))) -> L.Tr(R.mem(R.out5(a, b), R.fire5(a, b, ts))):
  RM.mem_append_l(R.out5(a, b), R.guard(R.hit5(a, b), R.one(R.out5(a, b))), R.fire6(a, b, ts), RG.guard_has(R.hit5(a, b), R.one(R.out5(a, b)), R.out5(a, b), h, RG.one_has(R.out5(a, b))))

# has5: prp-inv1's conclusion is in fire when its guard holds.
def has5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit5(a, b))) -> L.Tr(R.mem(R.out5(a, b), R.fire(a, b, ts))):
  up1(a, b, ts, R.out5(a, b), up2(a, b, ts, R.out5(a, b), up3(a, b, ts, R.out5(a, b), up4(a, b, ts, R.out5(a, b), here5(a, b, ts, h)))))

def here6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit6(a, b))) -> L.Tr(R.mem(R.out6(a, b), R.fire6(a, b, ts))):
  RM.mem_append_l(R.out6(a, b), R.guard(R.hit6(a, b), R.one(R.out6(a, b))), R.fire7(a, b, ts), RG.guard_has(R.hit6(a, b), R.one(R.out6(a, b)), R.out6(a, b), h, RG.one_has(R.out6(a, b))))

# has6: prp-inv2's conclusion is in fire when its guard holds.
def has6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit6(a, b))) -> L.Tr(R.mem(R.out6(a, b), R.fire(a, b, ts))):
  up1(a, b, ts, R.out6(a, b), up2(a, b, ts, R.out6(a, b), up3(a, b, ts, R.out6(a, b), up4(a, b, ts, R.out6(a, b), up5(a, b, ts, R.out6(a, b), here6(a, b, ts, h))))))

def here7(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit7(a, b, ts))) -> L.Tr(R.mem(R.out7(a, b), R.fire7(a, b, ts))):
  RG.guard_has(R.hit7(a, b, ts), R.one(R.out7(a, b)), R.out7(a, b), h, RG.one_has(R.out7(a, b)))

# has7: prp-trp's conclusion is in fire when its guard holds.
def has7(+a: R.Tri, +b: R.Tri, +ts: R.Ts, h: L.Tr(R.hit7(a, b, ts))) -> L.Tr(R.mem(R.out7(a, b), R.fire(a, b, ts))):
  up1(a, b, ts, R.out7(a, b), up2(a, b, ts, R.out7(a, b), up3(a, b, ts, R.out7(a, b), up4(a, b, ts, R.out7(a, b), up5(a, b, ts, R.out7(a, b), up6(a, b, ts, R.out7(a, b), here7(a, b, ts, h)))))))

def In1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit1(a, b)) & {c == R.out1(a, b) : R.Tri}

def In2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit2(a, b)) & {c == R.out2(a, b) : R.Tri}

def In3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit3(a, b)) & {c == R.out3(a, b) : R.Tri}

def In4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit4(a, b)) & {c == R.out4(a, b) : R.Tri}

def In5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit5(a, b)) & {c == R.out5(a, b) : R.Tri}

def In6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit6(a, b)) & {c == R.out6(a, b) : R.Tri}

def In7(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  L.Tr(R.hit7(a, b, ts)) & {c == R.out7(a, b) : R.Tri}

def Sum7(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  In7(a, b, ts, c)

def Sum6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  Or(In6(a, b, ts, c), Sum7(a, b, ts, c))

def Sum5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  Or(In5(a, b, ts, c), Sum6(a, b, ts, c))

def Sum4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  Or(In4(a, b, ts, c), Sum5(a, b, ts, c))

def Sum3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  Or(In3(a, b, ts, c), Sum4(a, b, ts, c))

def Sum2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  Or(In2(a, b, ts, c), Sum3(a, b, ts, c))

def Sum1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri) -> Type:
  Or(In1(a, b, ts, c), Sum2(a, b, ts, c))

def stage7(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire7(a, b, ts)))) -> Sum7(a, b, ts, c):
  RG.guard_elim(R.hit7(a, b, ts), R.one(R.out7(a, b)), c, p, In7(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out7(a, b), m)))

def stage6(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, r: Or(L.Tr(R.mem(c, R.guard(R.hit6(a, b), R.one(R.out6(a, b))))), L.Tr(R.mem(c, R.fire7(a, b, ts))))) -> Sum6(a, b, ts, c):
  match r:
    case Inl{q}:
      Inl{RG.guard_elim(R.hit6(a, b), R.one(R.out6(a, b)), c, q, In6(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out6(a, b), m)))}
    case Inr{q}:
      Inr{stage7(a, b, ts, c, q)}

def stage5(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, r: Or(L.Tr(R.mem(c, R.guard(R.hit5(a, b), R.one(R.out5(a, b))))), L.Tr(R.mem(c, R.fire6(a, b, ts))))) -> Sum5(a, b, ts, c):
  match r:
    case Inl{q}:
      Inl{RG.guard_elim(R.hit5(a, b), R.one(R.out5(a, b)), c, q, In5(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out5(a, b), m)))}
    case Inr{q}:
      Inr{stage6(a, b, ts, c, RM.mem_append_elim(c, R.guard(R.hit6(a, b), R.one(R.out6(a, b))), R.fire7(a, b, ts), q))}

def stage4(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, r: Or(L.Tr(R.mem(c, R.guard(R.hit4(a, b), R.one(R.out4(a, b))))), L.Tr(R.mem(c, R.fire5(a, b, ts))))) -> Sum4(a, b, ts, c):
  match r:
    case Inl{q}:
      Inl{RG.guard_elim(R.hit4(a, b), R.one(R.out4(a, b)), c, q, In4(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out4(a, b), m)))}
    case Inr{q}:
      Inr{stage5(a, b, ts, c, RM.mem_append_elim(c, R.guard(R.hit5(a, b), R.one(R.out5(a, b))), R.fire6(a, b, ts), q))}

def stage3(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, r: Or(L.Tr(R.mem(c, R.guard(R.hit3(a, b), R.one(R.out3(a, b))))), L.Tr(R.mem(c, R.fire4(a, b, ts))))) -> Sum3(a, b, ts, c):
  match r:
    case Inl{q}:
      Inl{RG.guard_elim(R.hit3(a, b), R.one(R.out3(a, b)), c, q, In3(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out3(a, b), m)))}
    case Inr{q}:
      Inr{stage4(a, b, ts, c, RM.mem_append_elim(c, R.guard(R.hit4(a, b), R.one(R.out4(a, b))), R.fire5(a, b, ts), q))}

def stage2(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, r: Or(L.Tr(R.mem(c, R.guard(R.hit2(a, b), R.one(R.out2(a, b))))), L.Tr(R.mem(c, R.fire3(a, b, ts))))) -> Sum2(a, b, ts, c):
  match r:
    case Inl{q}:
      Inl{RG.guard_elim(R.hit2(a, b), R.one(R.out2(a, b)), c, q, In2(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out2(a, b), m)))}
    case Inr{q}:
      Inr{stage3(a, b, ts, c, RM.mem_append_elim(c, R.guard(R.hit3(a, b), R.one(R.out3(a, b))), R.fire4(a, b, ts), q))}

def stage1(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, r: Or(L.Tr(R.mem(c, R.guard(R.hit1(a, b), R.one(R.out1(a, b))))), L.Tr(R.mem(c, R.fire2(a, b, ts))))) -> Sum1(a, b, ts, c):
  match r:
    case Inl{q}:
      Inl{RG.guard_elim(R.hit1(a, b), R.one(R.out1(a, b)), c, q, In1(a, b, ts, c), h => m => (h, RG.one_elim(c, R.out1(a, b), m)))}
    case Inr{q}:
      Inr{stage2(a, b, ts, c, RM.mem_append_elim(c, R.guard(R.hit2(a, b), R.one(R.out2(a, b))), R.fire3(a, b, ts), q))}

# fire_cases: a conclusion in fire(a, b) came from one of the seven guards.
def fire_cases(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fire(a, b, ts)))) -> Sum1(a, b, ts, c):
  stage1(a, b, ts, c, RM.mem_append_elim(c, R.guard(R.hit1(a, b), R.one(R.out1(a, b))), R.fire2(a, b, ts), p))

def tr1(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In1(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 0n) & (Sp.Eqn(ob, sa) & Sp.Concl(c, sb, 0n, oa)))):
  (hit, ceq) = i
  L.and_elim(S.and(S.neq(pa, 1n), S.neq(pb, 0n)), S.neq(ob, sa), hit, {c == R.T{sb, 0n, oa} : R.Tri}, ceq, (Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 0n) & (Sp.Eqn(ob, sa) & Sp.Concl(c, sb, 0n, oa)))), ceq1 => hab => h3 => L.and_elim(S.neq(pa, 1n), S.neq(pb, 0n), hab, {c == R.T{sb, 0n, oa} : R.Tri}, ceq1, (Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 0n) & (Sp.Eqn(ob, sa) & Sp.Concl(c, sb, 0n, oa)))), ceq2 => h1 => h2 => (L.neq_sound(pa, 1n, h1), (L.neq_sound(pb, 0n, h2), (L.neq_sound(ob, sa, h3), ceq2)))))

def tr2(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In2(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 1n) & (Sp.Eqn(sb, oa) & Sp.Concl(c, sa, 1n, ob)))):
  (hit, ceq) = i
  L.and_elim(S.and(S.neq(pa, 1n), S.neq(pb, 1n)), S.neq(sb, oa), hit, {c == R.T{sa, 1n, ob} : R.Tri}, ceq, (Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 1n) & (Sp.Eqn(sb, oa) & Sp.Concl(c, sa, 1n, ob)))), ceq1 => hab => h3 => L.and_elim(S.neq(pa, 1n), S.neq(pb, 1n), hab, {c == R.T{sa, 1n, ob} : R.Tri}, ceq1, (Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 1n) & (Sp.Eqn(sb, oa) & Sp.Concl(c, sa, 1n, ob)))), ceq2 => h1 => h2 => (L.neq_sound(pa, 1n, h1), (L.neq_sound(pb, 1n, h2), (L.neq_sound(sb, oa, h3), ceq2)))))

def tr3(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In3(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, 2n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, sb, 0n, oa))):
  (hit, ceq) = i
  L.and_elim(S.neq(pa, 2n), S.neq(pb, sa), hit, {c == R.T{sb, 0n, oa} : R.Tri}, ceq, (Sp.Eqn(pa, 2n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, sb, 0n, oa))), ceq1 => h1 => h2 => (L.neq_sound(pa, 2n, h1), (L.neq_sound(pb, sa, h2), ceq1)))

def tr4(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In4(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, 3n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, 0n, oa))):
  (hit, ceq) = i
  L.and_elim(S.neq(pa, 3n), S.neq(pb, sa), hit, {c == R.T{ob, 0n, oa} : R.Tri}, ceq, (Sp.Eqn(pa, 3n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, 0n, oa))), ceq1 => h1 => h2 => (L.neq_sound(pa, 3n, h1), (L.neq_sound(pb, sa, h2), ceq1)))

def tr5(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In5(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))):
  (hit, ceq) = i
  L.and_elim(S.neq(pa, 4n), S.neq(pb, sa), hit, {c == R.T{ob, oa, sb} : R.Tri}, ceq, (Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))), ceq1 => h1 => h2 => (L.neq_sound(pa, 4n, h1), (L.neq_sound(pb, sa, h2), ceq1)))

def tr6(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In6(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))):
  (hit, ceq) = i
  L.and_elim(S.neq(pa, 4n), S.neq(pb, oa), hit, {c == R.T{ob, sa, sb} : R.Tri}, ceq, (Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), ceq1 => h1 => h2 => (L.neq_sound(pa, 4n, h1), (L.neq_sound(pb, oa, h2), ceq1)))

def tr7(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, i: In7(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob)))):
  (hit, ceq) = i
  L.and_elim(S.and(S.neq(pa, pb), S.neq(oa, sb)), R.mem(R.T{pa, 0n, 5n}, ts), hit, {c == R.T{sa, pa, ob} : R.Tri}, ceq, (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob)))), ceq1 => hab => h3 => L.and_elim(S.neq(pa, pb), S.neq(oa, sb), hab, {c == R.T{sa, pa, ob} : R.Tri}, ceq1, (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob)))), ceq2 => h1 => h2 => (L.neq_sound(pa, pb, h1), (L.neq_sound(oa, sb, h2), (h3, ceq2)))))

def rs6(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, s: Sum6(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob))))):
  match s:
    case Inl{x}:
      Inl{tr6(sa, pa, oa, sb, pb, ob, ts, c, x)}
    case Inr{y}:
      Inr{tr7(sa, pa, oa, sb, pb, ob, ts, c, y)}

def rs5(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, s: Sum5(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob)))))):
  match s:
    case Inl{x}:
      Inl{tr5(sa, pa, oa, sb, pb, ob, ts, c, x)}
    case Inr{y}:
      Inr{rs6(sa, pa, oa, sb, pb, ob, ts, c, y)}

def rs4(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, s: Sum4(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> Or((Sp.Eqn(pa, 3n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, 0n, oa))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob))))))):
  match s:
    case Inl{x}:
      Inl{tr4(sa, pa, oa, sb, pb, ob, ts, c, x)}
    case Inr{y}:
      Inr{rs5(sa, pa, oa, sb, pb, ob, ts, c, y)}

def rs3(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, s: Sum3(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> Or((Sp.Eqn(pa, 2n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, sb, 0n, oa))), Or((Sp.Eqn(pa, 3n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, 0n, oa))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob)))))))):
  match s:
    case Inl{x}:
      Inl{tr3(sa, pa, oa, sb, pb, ob, ts, c, x)}
    case Inr{y}:
      Inr{rs4(sa, pa, oa, sb, pb, ob, ts, c, y)}

def rs2(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, s: Sum2(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> Or((Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 1n) & (Sp.Eqn(sb, oa) & Sp.Concl(c, sa, 1n, ob)))), Or((Sp.Eqn(pa, 2n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, sb, 0n, oa))), Or((Sp.Eqn(pa, 3n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, 0n, oa))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob))))))))):
  match s:
    case Inl{x}:
      Inl{tr2(sa, pa, oa, sb, pb, ob, ts, c, x)}
    case Inr{y}:
      Inr{rs3(sa, pa, oa, sb, pb, ob, ts, c, y)}

def rs1(+sa: Nat, +pa: Nat, +oa: Nat, +sb: Nat, +pb: Nat, +ob: Nat, +ts: R.Ts, +c: R.Tri, s: Sum1(R.T{sa, pa, oa}, R.T{sb, pb, ob}, ts, c)) -> Or((Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 0n) & (Sp.Eqn(ob, sa) & Sp.Concl(c, sb, 0n, oa)))), Or((Sp.Eqn(pa, 1n) & (Sp.Eqn(pb, 1n) & (Sp.Eqn(sb, oa) & Sp.Concl(c, sa, 1n, ob)))), Or((Sp.Eqn(pa, 2n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, sb, 0n, oa))), Or((Sp.Eqn(pa, 3n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, 0n, oa))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, sa) & Sp.Concl(c, ob, oa, sb))), Or((Sp.Eqn(pa, 4n) & (Sp.Eqn(pb, oa) & Sp.Concl(c, ob, sa, sb))), (Sp.Eqn(pa, pb) & (Sp.Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Sp.Concl(c, sa, pa, ob)))))))))):
  match s:
    case Inl{x}:
      Inl{tr1(sa, pa, oa, sb, pb, ob, ts, c, x)}
    case Inr{y}:
      Inr{rs2(sa, pa, oa, sb, pb, ob, ts, c, y)}

# rule_sound: a conclusion of fire satisfies the rule table.
def rule_sound(+a: R.Tri, +b: R.Tri, +ts: R.Ts, +c: R.Tri, s: Sum1(a, b, ts, c)) -> Sp.Rule(a, b, c, ts):
  match a b:
    case R.T{+sa, +pa, +oa} R.T{+sb, +pb, +ob}:
      rs1(sa, pa, oa, sb, pb, ob, ts, c, s)

def main() -> U32:
  1
