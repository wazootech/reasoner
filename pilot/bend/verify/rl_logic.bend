# Triple equality in the six-rule model: reflexive, and sound (the Bool test
# `tri_eq` being true means the triples are equal). Mirrors edge_eq in logic.bend.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L

def tri_eq_refl(+e: R.Tri) -> L.Tr(R.tri_eq(e, e)):
  match e:
    case R.T{+a, +b, +c}:
      L.and_intro(S.and(S.neq(a, a), S.neq(b, b)), S.neq(c, c),
        L.and_intro(S.neq(a, a), S.neq(b, b), L.neq_refl(a), L.neq_refl(b)),
        L.neq_refl(c))

def tri_eq_from(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, had: L.Tr(S.neq(a, d)), hbe: L.Tr(S.neq(b, e)), hcf: L.Tr(S.neq(c, f))) -> {R.T{a, b, c} == R.T{d, e, f} : R.Tri}:
  ad = L.neq_sound(a, d, had)
  be = L.neq_sound(b, e, hbe)
  cf = L.neq_sound(c, f, hcf)
  %cf : {R.T{a, b, c} == R.T{d, e, _} : R.Tri}
  %be : {R.T{a, b, c} == R.T{d, _, c} : R.Tri}
  %ad : {R.T{a, b, c} == R.T{_, b, c} : R.Tri}
  {==}

def tri_eq_sound(+x: R.Tri, +y: R.Tri, h: L.Tr(R.tri_eq(x, y))) -> {x == y : R.Tri}:
  match x y:
    case R.T{+a, +b, +c} R.T{+d, +e, +f}:
      L.and_elim(S.and(S.neq(a, d), S.neq(b, e)), S.neq(c, f), h, Unit, Unit{}, {R.T{a, b, c} == R.T{d, e, f} : R.Tri},
        u => hab => hcf => L.and_elim(S.neq(a, d), S.neq(b, e), hab, L.Tr(S.neq(c, f)), hcf, {R.T{a, b, c} == R.T{d, e, f} : R.Tri},
          hcf1 => had => hbe => tri_eq_from(a, b, c, d, e, f, had, hbe, hcf1)))

def main() -> U32:
  1
