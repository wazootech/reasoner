# Proofs of LAWS.bend. `bend PROOF.bend --verdict` is the gate.
import Base
import ./sco.bend as S
import ./LAWS.bend as Laws
import ./mem.bend as M
import ./compose.bend as C

def Laws.step_mono(e, es, p):
  M.mem_append_l(e, es, S.compose(es, es), p)

def Laws.step_closes(a, b, c, es, p, q):
  M.mem_append_r(S.E{a, c}, es, S.compose(es, es), C.compose_has(a, b, c, es, es, p, q))
