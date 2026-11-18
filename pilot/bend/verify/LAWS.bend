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

# Soundness: whatever a round adds is a composition of two edges already there.
law step_sound:
  for +a: Nat
  for +c: Nat
  for +es: S.Es
  for p: {S.mem(S.E{a, c}, S.step(es)) == True{} : Bool}
  Or({S.mem(S.E{a, c}, es) == True{} : Bool}, &b: Nat -> ({S.mem(S.E{a, b}, es) == True{} : Bool} & {S.mem(S.E{b, c}, es) == True{} : Bool}))

# If a round adds nothing new, the graph is transitively closed. This is what
# the fixpoint loop relies on when it stops.
law stable_is_closed:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +es: S.Es
  for stable: @e: S.Edge -> ({S.mem(e, S.step(es)) == True{} : Bool} -> {S.mem(e, es) == True{} : Bool})
  for p: {S.mem(S.E{a, b}, es) == True{} : Bool}
  for q: {S.mem(S.E{b, c}, es) == True{} : Bool}
  {S.mem(S.E{a, c}, es) == True{} : Bool}

# The loop, `iter(n, es)`: n rounds. It never drops an input edge.
law iter_keeps_input:
  for +n: Nat
  for +es: S.Es
  for +e: S.Edge
  for p: {S.mem(e, es) == True{} : Bool}
  {S.mem(e, S.iter(n, es)) == True{} : Bool}

# If the stop test `subset(step(r), r)` passes on the result r of n rounds, then
# r is transitively closed. The test, not a proof of termination, is what a
# caller checks: Bend proves the answer is right whenever the test passes.
law stop_means_closed:
  for +n: Nat
  for +es: S.Es
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for stop: {S.subset(S.step(S.iter(n, es)), S.iter(n, es)) == True{} : Bool}
  for p: {S.mem(S.E{a, b}, S.iter(n, es)) == True{} : Bool}
  for q: {S.mem(S.E{b, c}, S.iter(n, es)) == True{} : Bool}
  {S.mem(S.E{a, c}, S.iter(n, es)) == True{} : Bool}
