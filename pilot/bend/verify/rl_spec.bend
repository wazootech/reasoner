# The six-rule table as a type: Rule(a, b, c, ts) says c is a conclusion of one
# of the seven rules whose premises are a and b (the seventh, prp-trp, also needs
# (p type TransitiveProperty) in ts). Written in fields, not in terms of the
# model's guards, so it is an independent statement of the rules.
import Base
import ./rl.bend as R
import ./logic.bend as L

def Eqn(+x: Nat, +y: Nat) -> Type:
  {x == y : Nat}

def Concl(+c: R.Tri, +x: Nat, +y: Nat, +z: Nat) -> Type:
  {c == R.T{x, y, z} : R.Tri}

def Rule(+a: R.Tri, +b: R.Tri, +c: R.Tri, +ts: R.Ts) -> Type:
  match a b:
    case R.T{+sa, +pa, +oa} R.T{+sb, +pb, +ob}:
      Or((Eqn(pa, 1n) & (Eqn(pb, 0n) & (Eqn(ob, sa) & Concl(c, sb, 0n, oa)))), Or((Eqn(pa, 1n) & (Eqn(pb, 1n) & (Eqn(sb, oa) & Concl(c, sa, 1n, ob)))), Or((Eqn(pa, 2n) & (Eqn(pb, sa) & Concl(c, sb, 0n, oa))), Or((Eqn(pa, 3n) & (Eqn(pb, sa) & Concl(c, ob, 0n, oa))), Or((Eqn(pa, 4n) & (Eqn(pb, sa) & Concl(c, ob, oa, sb))), Or((Eqn(pa, 4n) & (Eqn(pb, oa) & Concl(c, ob, sa, sb))), (Eqn(pa, pb) & (Eqn(oa, sb) & (L.Tr(R.mem(R.T{pa, 0n, 5n}, ts)) & Concl(c, sa, pa, ob))))))))))

def main() -> U32:
  1
