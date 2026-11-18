# Lemmas about fresh_go(xs, base, acc), which collects the triples of xs that
# base lacks, each once: it keeps `acc` (fresh_acc), returns only members of xs
# or acc (fresh_sound), and misses nothing that base lacks (fresh_complete).
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_logic.bend as RL
import ./rl_mem.bend as RM
import ./rl_dedupe.bend as RD

def fresh_acc(+xs: R.Ts, +base: R.Ts, +acc: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, acc))) -> L.Tr(R.mem(c, R.fresh_go(xs, base, acc))):
  match xs:
    case R.TNil{}:
      p
    case R.TCons{+h, +t}:
      fresh_acc(t, R.insert(h, base), R.insert_if(R.mem(h, base), h, acc), c, RD.insert_if_keeps(R.mem(h, base), c, h, acc, p))

def fs_ins(+c: R.Tri, +h: R.Tri, +t: R.Ts, +acc: R.Ts, r: Or(L.Tr(R.mem(c, acc)), L.Tr(R.tri_eq(c, h)))) -> Or(L.Tr(R.mem(c, R.TCons{h, t})), L.Tr(R.mem(c, acc))):
  match r:
    case Inl{a}:
      Inr{a}
    case Inr{b}:
      Inl{L.or_l(R.tri_eq(c, h), R.mem(c, t), b)}

def fs_cases(+c: R.Tri, +h: R.Tri, +t: R.Ts, +base: R.Ts, +acc: R.Ts, r: Or(L.Tr(R.mem(c, t)), L.Tr(R.mem(c, R.insert_if(R.mem(h, base), h, acc))))) -> Or(L.Tr(R.mem(c, R.TCons{h, t})), L.Tr(R.mem(c, acc))):
  match r:
    case Inl{q}:
      Inl{L.or_r(R.tri_eq(c, h), R.mem(c, t), q)}
    case Inr{q}:
      fs_ins(c, h, t, acc, RD.insert_if_elim(R.mem(h, base), c, h, acc, q))

# fresh_sound: what fresh_go returns came from xs or acc.
def fresh_sound(+xs: R.Ts, +base: R.Ts, +acc: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, R.fresh_go(xs, base, acc)))) -> Or(L.Tr(R.mem(c, xs)), L.Tr(R.mem(c, acc))):
  match xs:
    case R.TNil{}:
      Inr{p}
    case R.TCons{+h, +t}:
      fs_cases(c, h, t, base, acc, fresh_sound(t, R.insert(h, base), R.insert_if(R.mem(h, base), h, acc), c, p))

# fc_head: c equals h. If h was already in base, so is c; if not, h went into acc
# and fresh_go keeps it. `hit` is the test, generalised so Bend can match on it.
def fc_head(+hit: Bool, +h: R.Tri, +c: R.Tri, +base: R.Ts, +acc: R.Ts, +t: R.Ts, eq: {R.mem(h, base) == hit : Bool}, q: L.Tr(R.tri_eq(c, h))) -> Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(t, R.insert(h, base), R.insert_if(hit, h, acc))))):
  match hit:
    case True{}:
      Inl{RM.mem_tri_eq(c, h, base, q, eq)}
    case False{}:
      Inr{fresh_acc(t, R.insert(h, base), R.TCons{h, acc}, c, RM.mem_tri_eq(c, h, R.TCons{h, acc}, q, RM.mem_head(h, acc)))}

def fc_eq(+h: R.Tri, +c: R.Tri, +base: R.Ts, +acc: R.Ts, +t: R.Ts, q: L.Tr(R.tri_eq(c, h))) -> Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(R.TCons{h, t}, base, acc)))):
  fc_head(R.mem(h, base), h, c, base, acc, t, {==}, q)

def fc_ins(+c: R.Tri, +h: R.Tri, +t: R.Ts, +base: R.Ts, +acc: R.Ts, r: Or(L.Tr(R.mem(c, base)), L.Tr(R.tri_eq(c, h)))) -> Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(R.TCons{h, t}, base, acc)))):
  match r:
    case Inl{x}:
      Inl{x}
    case Inr{y}:
      fc_eq(h, c, base, acc, t, y)

def fc_rec(+c: R.Tri, +h: R.Tri, +t: R.Ts, +base: R.Ts, +acc: R.Ts, r: Or(L.Tr(R.mem(c, R.insert(h, base))), L.Tr(R.mem(c, R.fresh_go(t, R.insert(h, base), R.insert_if(R.mem(h, base), h, acc)))))) -> Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(R.TCons{h, t}, base, acc)))):
  match r:
    case Inl{a}:
      fc_ins(c, h, t, base, acc, RD.insert_elim(c, h, base, a))
    case Inr{q}:
      Inr{q}

# fresh_complete: a member of xs is in base or in what fresh_go returns.
def fresh_complete(+xs: R.Ts, +base: R.Ts, +acc: R.Ts, +c: R.Tri, p: L.Tr(R.mem(c, xs))) -> Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(xs, base, acc)))):
  match xs:
    case R.TNil{}:
      Empty.absurd(Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(R.TNil{}, base, acc)))), L.false_ne_true(p))
    case R.TCons{+h, +t}:
      L.or_elim(R.tri_eq(c, h), R.mem(c, t), p, Unit, Unit{},
        Or(L.Tr(R.mem(c, base)), L.Tr(R.mem(c, R.fresh_go(R.TCons{h, t}, base, acc)))),
        u => q => fc_eq(h, c, base, acc, t, q),
        u => q => fc_rec(c, h, t, base, acc, fresh_complete(t, R.insert(h, base), R.insert_if(R.mem(h, base), h, acc), c, q)))

def main() -> U32:
  1
