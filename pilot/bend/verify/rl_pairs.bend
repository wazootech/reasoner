# pairs_has and pairs_elim: a triple is in `pairs(xs, ys, ts)` exactly when some
# a in xs and b in ys fire it. This is the six-rule version of compose_has and
# compose_elim; every rule's completeness and soundness goes through it.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_logic.bend as RL
import ./rl_mem.bend as RM

def pairs1_head(+a: R.Tri, +b: R.Tri, +c: R.Tri, +h: R.Tri, +t: R.Ts, +ts: R.Ts, q: L.Tr(R.tri_eq(b, h)), hc: L.Tr(R.mem(c, R.fire(a, b, ts)))) -> L.Tr(R.mem(c, R.append(R.fire(a, h, ts), R.pairs1(a, t, ts)))):
  e = RL.tri_eq_sound(b, h, q)
  %e : L.Tr(R.mem(c, R.append(R.fire(a, _, ts), R.pairs1(a, t, ts))))
  RM.mem_append_l(c, R.fire(a, b, ts), R.pairs1(a, t, ts), hc)

# pairs1_has: b in ys and c in fire(a, b) put c in pairs1(a, ys).
def pairs1_has(+a: R.Tri, +b: R.Tri, +c: R.Tri, +ys: R.Ts, +ts: R.Ts, hb: L.Tr(R.mem(b, ys)), hc: L.Tr(R.mem(c, R.fire(a, b, ts)))) -> L.Tr(R.mem(c, R.pairs1(a, ys, ts))):
  match ys:
    case R.TNil{}:
      Empty.absurd(L.Tr(R.mem(c, R.pairs1(a, R.TNil{}, ts))), L.false_ne_true(hb))
    case R.TCons{+h, +t}:
      L.or_elim(R.tri_eq(b, h), R.mem(b, t), hb, L.Tr(R.mem(c, R.fire(a, b, ts))), hc,
        L.Tr(R.mem(c, R.append(R.fire(a, h, ts), R.pairs1(a, t, ts)))),
        hc1 => q => pairs1_head(a, b, c, h, t, ts, q, hc1),
        hc1 => q => RM.mem_append_r(c, R.fire(a, h, ts), R.pairs1(a, t, ts), pairs1_has(a, b, c, t, ts, q, hc1)))

def Both(+b: R.Tri, +c: R.Tri, +a: R.Tri, +ys: R.Ts, +ts: R.Ts) -> Type:
  L.Tr(R.mem(b, ys)) & L.Tr(R.mem(c, R.fire(a, b, ts)))

def pairs_head(+a: R.Tri, +b: R.Tri, +c: R.Tri, +h: R.Tri, +t: R.Ts, +ys: R.Ts, +ts: R.Ts, q: L.Tr(R.tri_eq(a, h)), cx: Both(b, c, a, ys, ts)) -> L.Tr(R.mem(c, R.append(R.pairs1(h, ys, ts), R.pairs(t, ys, ts)))):
  (hb, hc) = cx
  e = RL.tri_eq_sound(a, h, q)
  %e : L.Tr(R.mem(c, R.append(R.pairs1(_, ys, ts), R.pairs(t, ys, ts))))
  RM.mem_append_l(c, R.pairs1(a, ys, ts), R.pairs(t, ys, ts), pairs1_has(a, b, c, ys, ts, hb, hc))

# pairs_has: a in xs, b in ys and c in fire(a, b) put c in pairs(xs, ys).
def pairs_has(+a: R.Tri, +b: R.Tri, +c: R.Tri, +xs: R.Ts, +ys: R.Ts, +ts: R.Ts, ha: L.Tr(R.mem(a, xs)), cx: Both(b, c, a, ys, ts)) -> L.Tr(R.mem(c, R.pairs(xs, ys, ts))):
  match xs:
    case R.TNil{}:
      Empty.absurd(L.Tr(R.mem(c, R.pairs(R.TNil{}, ys, ts))), L.false_ne_true(ha))
    case R.TCons{+h, +t}:
      L.or_elim(R.tri_eq(a, h), R.mem(a, t), ha, Both(b, c, a, ys, ts), cx,
        L.Tr(R.mem(c, R.append(R.pairs1(h, ys, ts), R.pairs(t, ys, ts)))),
        cx1 => q => pairs_head(a, b, c, h, t, ys, ts, q, cx1),
        cx1 => q => RM.mem_append_r(c, R.pairs1(h, ys, ts), R.pairs(t, ys, ts), pairs_has(a, b, c, t, ys, ts, q, cx1)))

# WB: a partner b in ys that fires c with a.
def WB(+c: R.Tri, +a: R.Tri, +ys: R.Ts, +ts: R.Ts) -> Type:
  &b: R.Tri -> (L.Tr(R.mem(b, ys)) & L.Tr(R.mem(c, R.fire(a, b, ts))))

def wb_tail(+c: R.Tri, +a: R.Tri, +h: R.Tri, +t: R.Ts, +ts: R.Ts, w: WB(c, a, t, ts)) -> WB(c, a, R.TCons{h, t}, ts):
  (+b, m) = w
  (m1, m2) = m
  (b, (RM.mem_tail(b, h, t, m1), m2))

def pairs1_cases(+c: R.Tri, +a: R.Tri, +h: R.Tri, +t: R.Ts, +ts: R.Ts, r: Or(L.Tr(R.mem(c, R.fire(a, h, ts))), L.Tr(R.mem(c, R.pairs1(a, t, ts)))), rec: L.Tr(R.mem(c, R.pairs1(a, t, ts))) -> WB(c, a, t, ts)) -> WB(c, a, R.TCons{h, t}, ts):
  match r:
    case Inl{q}:
      (h, (RM.mem_head(h, t), q))
    case Inr{q}:
      wb_tail(c, a, h, t, ts, rec(q))

# pairs1_elim: a member of pairs1(a, ys) comes from some b in ys.
def pairs1_elim(+c: R.Tri, +a: R.Tri, +ys: R.Ts, +ts: R.Ts, p: L.Tr(R.mem(c, R.pairs1(a, ys, ts)))) -> WB(c, a, ys, ts):
  match ys:
    case R.TNil{}:
      Empty.absurd(WB(c, a, R.TNil{}, ts), L.false_ne_true(p))
    case R.TCons{+h, +t}:
      pairs1_cases(c, a, h, t, ts,
        RM.mem_append_elim(c, R.fire(a, h, ts), R.pairs1(a, t, ts), p),
        q => pairs1_elim(c, a, t, ts, q))

# WA: a partner a in xs and a b in ys that together fire c.
def WA(+c: R.Tri, +xs: R.Ts, +ys: R.Ts, +ts: R.Ts) -> Type:
  &a: R.Tri -> (L.Tr(R.mem(a, xs)) & WB(c, a, ys, ts))

def wa_tail(+c: R.Tri, +h: R.Tri, +t: R.Ts, +ys: R.Ts, +ts: R.Ts, w: WA(c, t, ys, ts)) -> WA(c, R.TCons{h, t}, ys, ts):
  (+a, m) = w
  (m1, m2) = m
  (a, (RM.mem_tail(a, h, t, m1), m2))

def pairs_cases(+c: R.Tri, +h: R.Tri, +t: R.Ts, +ys: R.Ts, +ts: R.Ts, r: Or(L.Tr(R.mem(c, R.pairs1(h, ys, ts))), L.Tr(R.mem(c, R.pairs(t, ys, ts)))), rec: L.Tr(R.mem(c, R.pairs(t, ys, ts))) -> WA(c, t, ys, ts)) -> WA(c, R.TCons{h, t}, ys, ts):
  match r:
    case Inl{q}:
      (h, (RM.mem_head(h, t), pairs1_elim(c, h, ys, ts, q)))
    case Inr{q}:
      wa_tail(c, h, t, ys, ts, rec(q))

# pairs_elim: a member of pairs(xs, ys) comes from some a in xs and b in ys.
def pairs_elim(+c: R.Tri, +xs: R.Ts, +ys: R.Ts, +ts: R.Ts, p: L.Tr(R.mem(c, R.pairs(xs, ys, ts)))) -> WA(c, xs, ys, ts):
  match xs:
    case R.TNil{}:
      Empty.absurd(WA(c, R.TNil{}, ys, ts), L.false_ne_true(p))
    case R.TCons{+h, +t}:
      pairs_cases(c, h, t, ys, ts,
        RM.mem_append_elim(c, R.pairs1(h, ys, ts), R.pairs(t, ys, ts), p),
        q => pairs_elim(c, t, ys, ts, q))

def main() -> U32:
  1
