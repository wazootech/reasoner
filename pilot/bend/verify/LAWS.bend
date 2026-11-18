# The claims about scm-sco (rdfs:subClassOf transitivity). A human states
# these; PROOF.bend proves them, one def per law. `step` is one naive round.
import Base
import ./sco.bend as S

# One round never loses an edge.
law step_mono:
  for +e: S.Edge
  for +es: S.Es
  for p: {S.mem(e, es) == True{} : Bool}
  {S.mem(e, S.step(es)) == True{} : Bool}

# If a -> b and b -> c are both present, the next round has a -> c.
law step_closes:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +es: S.Es
  for p: {S.mem(S.E{a, b}, es) == True{} : Bool}
  for q: {S.mem(S.E{b, c}, es) == True{} : Bool}
  {S.mem(S.E{a, c}, S.step(es)) == True{} : Bool}
