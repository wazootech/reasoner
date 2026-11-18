# Proofs of LAWS.bend. `bend PROOF.bend --verdict` is the gate.
import Base
import ./sco.bend as S
import ./logic.bend as L
import ./LAWS.bend as Laws
import ./mem.bend as M
import ./compose.bend as C
import ./elim.bend as X
import ./loop.bend as Lp

def Laws.step_mono(e, es, p):
  M.mem_append_l(e, es, S.compose(es, es), p)

def Laws.step_closes(a, b, c, es, p, q):
  M.mem_append_r(S.E{a, c}, es, S.compose(es, es), C.compose_has(a, b, c, es, es, p, q))

def sound_cases(+a: Nat, +c: Nat, +es: S.Es, r: Or(L.Tr(S.mem(S.E{a, c}, es)), L.Tr(S.mem(S.E{a, c}, S.compose(es, es))))) -> Or(L.Tr(S.mem(S.E{a, c}, es)), X.Wit(a, c, es, es)):
  match r:
    case Inl{x}:
      Inl{x}
    case Inr{y}:
      Inr{X.compose_elim(a, c, es, es, y)}

def Laws.step_sound(a, c, es, p):
  sound_cases(a, c, es, X.mem_append_elim(S.E{a, c}, es, S.compose(es, es), p))

def Laws.stable_is_closed(a, b, c, es, stable, p, q):
  stable(S.E{a, c}, Laws.step_closes(a, b, c, es, p, q))

def Laws.iter_keeps_input(n, es, e, p):
  Lp.iter_contains(n, es, e, p)

def Laws.stop_means_closed(n, es, a, b, c, stop, p, q):
  Lp.sub_elim(S.E{a, c}, S.step(S.iter(n, es)), S.iter(n, es), stop, Laws.step_closes(a, b, c, S.iter(n, es), p, q))
