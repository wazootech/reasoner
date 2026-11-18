# The two loops agree. Both results contain the input; the naive result is the
# smallest stable superset (rl_least), and the semi-naive result is closed
# (rl_semiloop), so each is inside the other.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_dedupe.bend as RD
import ./rl_pairs.bend as RP
import ./rl_semi.bend as RS
import ./rl_loop.bend as RLp
import ./rl_sub.bend as Sb
import ./rl_pw.bend as RPw
import ./rl_least.bend as RLe
import ./rl_semiloop.bend as RSl

# ---- the input is inside the result, as a Bool subset

def kx(+cx: R.KeepCx) -> Bool:
  True{}

def kl0(+cx: R.KeepCx) -> R.Ts:
  match cx:
    case R.KeepCx{+n, +ts}:
      ts

# naive loop
def knt(+cx: R.KeepCx) -> R.Ts:
  match cx:
    case R.KeepCx{+n, +ts}:
      R.iter(n, ts)

def kng(+cx: R.KeepCx, +c: R.Tri, e: L.Tr(kx(cx)), m: L.Tr(R.mem(c, kl0(cx)))) -> L.Tr(R.mem(c, knt(cx))):
  match cx:
    case R.KeepCx{+n, +ts}:
      RLp.iter_contains(n, ts, c, m)

def keeps_sub(+n: Nat, +ts: R.Ts) -> L.Tr(R.subset(ts, R.iter(n, ts))):
  RPw.subset_pw(~R.KeepCx, ~kx, ~kl0, ~knt, ~kng, R.KeepCx{n, ts}, ts, ({==}, {==}), Sb.subset_refl(ts))

# semi-naive loop, started from old = TNil
def kst(+cx: R.KeepCx) -> R.Ts:
  match cx:
    case R.KeepCx{+n, +ts}:
      R.iter_semi(n, R.TNil{}, ts)

def ksg(+cx: R.KeepCx, +c: R.Tri, e: L.Tr(kx(cx)), m: L.Tr(R.mem(c, kl0(cx)))) -> L.Tr(R.mem(c, kst(cx))):
  match cx:
    case R.KeepCx{+n, +ts}:
      RSl.iter_semi_keeps(n, R.TNil{}, ts, c, RM.mem_append_l(c, ts, R.TNil{}, m))

def semi_keeps_sub(+n: Nat, +ts: R.Ts) -> L.Tr(R.subset(ts, R.iter_semi(n, R.TNil{}, ts))):
  RPw.subset_pw(~R.KeepCx, ~kx, ~kl0, ~kst, ~ksg, R.KeepCx{n, ts}, ts, ({==}, {==}), Sb.subset_refl(ts))

# ---- the semi-naive result is stable

def sfx(+cx: R.KeepCx) -> Bool:
  match cx:
    case R.KeepCx{+n, +ts}:
      R.semi_fixed(n, R.TNil{}, ts)

def sfl0(+cx: R.KeepCx) -> R.Ts:
  match cx:
    case R.KeepCx{+n, +ts}:
      R.step(R.iter_semi(n, R.TNil{}, ts))

def sft(+cx: R.KeepCx) -> R.Ts:
  match cx:
    case R.KeepCx{+n, +ts}:
      R.iter_semi(n, R.TNil{}, ts)

def sf_conv(+n: Nat, +ts: R.Ts, +c: R.Tri, e: L.Tr(R.semi_fixed(n, R.TNil{}, ts)), w: RP.WA(c, R.iter_semi(n, R.TNil{}, ts), R.iter_semi(n, R.TNil{}, ts), R.iter_semi(n, R.TNil{}, ts))) -> L.Tr(R.mem(c, R.iter_semi(n, R.TNil{}, ts))):
  (+a, m) = w
  (ma, wb) = m
  (+b, m2) = wb
  (mb, hf) = m2
  RSl.iter_semi_closed(n, R.TNil{}, ts, a, b, c, {==}, e, ma, mb, hf)

def sf_cases(+n: Nat, +ts: R.Ts, +c: R.Tri, e: L.Tr(R.semi_fixed(n, R.TNil{}, ts)), o: Or(L.Tr(R.mem(c, R.derive(R.iter_semi(n, R.TNil{}, ts)))), L.Tr(R.mem(c, R.iter_semi(n, R.TNil{}, ts))))) -> L.Tr(R.mem(c, R.iter_semi(n, R.TNil{}, ts))):
  match o:
    case Inl{q}:
      sf_conv(n, ts, c, e, RP.pairs_elim(c, R.iter_semi(n, R.TNil{}, ts), R.iter_semi(n, R.TNil{}, ts), R.iter_semi(n, R.TNil{}, ts), q))
    case Inr{x}:
      x

def sfg(+cx: R.KeepCx, +c: R.Tri, e: L.Tr(sfx(cx)), m: L.Tr(R.mem(c, sfl0(cx)))) -> L.Tr(R.mem(c, sft(cx))):
  match cx:
    case R.KeepCx{+n, +ts}:
      sf_cases(n, ts, c, e, RD.union_elim(c, R.derive(R.iter_semi(n, R.TNil{}, ts)), R.iter_semi(n, R.TNil{}, ts), m))

# semi_stable: when semi_fixed holds, a further naive round adds nothing.
def semi_stable(+n: Nat, +ts: R.Ts, fixed: L.Tr(R.semi_fixed(n, R.TNil{}, ts))) -> L.Tr(R.subset(R.step(R.iter_semi(n, R.TNil{}, ts)), R.iter_semi(n, R.TNil{}, ts))):
  RPw.subset_pw(~R.KeepCx, ~sfx, ~sfl0, ~sft, ~sfg, R.KeepCx{n, ts}, R.step(R.iter_semi(n, R.TNil{}, ts)),
    RS.dup(Bool, R.semi_fixed(n, R.TNil{}, ts), True{}, fixed),
    Sb.subset_refl(R.step(R.iter_semi(n, R.TNil{}, ts))))

# ---- the two directions

# naive_in_semi: the naive result is inside the semi-naive result.
def naive_in_semi(+n: Nat, +m: Nat, +ts: R.Ts, fixed: L.Tr(R.semi_fixed(m, R.TNil{}, ts))) -> L.Tr(R.subset(R.iter(n, ts), R.iter_semi(m, R.TNil{}, ts))):
  RLe.iter_least(n, ts, R.iter_semi(m, R.TNil{}, ts), semi_keeps_sub(m, ts),
    RS.dup(Bool, R.subset(R.step(R.iter_semi(m, R.TNil{}, ts)), R.iter_semi(m, R.TNil{}, ts)), True{}, semi_stable(m, ts, fixed)))

# semi_in_naive: the semi-naive result is inside the naive result.
def semi_in_naive(+n: Nat, +m: Nat, +ts: R.Ts, stop: L.Tr(R.subset(R.step(R.iter(n, ts)), R.iter(n, ts)))) -> L.Tr(R.subset(R.iter_semi(m, R.TNil{}, ts), R.iter(n, ts))):
  RSl.iter_semi_least(m, R.TNil{}, ts, R.iter(n, ts),
    L.and_intro(R.subset(R.append(ts, R.TNil{}), R.iter(n, ts)), R.subset(R.step(R.iter(n, ts)), R.iter(n, ts)),
      Sb.subset_append(ts, R.TNil{}, R.iter(n, ts), keeps_sub(n, ts), {==}), stop))

def main() -> U32:
  1
