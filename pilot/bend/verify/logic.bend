# Lemmas about sco.bend's Bool and edge helpers, proved by hand: Bend has no
# tactics, so each is a def whose type is the claim. `Tr(b)` says the Bool `b`
# is `True{}`.
import Base
import ./sco.bend as S

def Tr(+b: Bool) -> Type:
  {b == True{} : Bool}

# disc sends False to Empty and True to Unit, so a rewrite through it turns
# `False == True` into a proof of Empty.
def disc(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def false_ne_true(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : disc(_)
  Unit{}

def neq_refl(+a: Nat) -> Tr(S.neq(a, a)):
  match a:
    case 0n:
      {==}
    case 1n+p:
      neq_refl(p)

def neq_sound(+a: Nat, +b: Nat, h: Tr(S.neq(a, b))) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, false_ne_true(h))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, false_ne_true(h))
    case 1n+ap 1n+bp:
      %neq_sound(ap, bp, h) : {1n+ap == 1n+_ : Nat}
      {==}

def or_l(+a: Bool, +b: Bool, h: Tr(a)) -> Tr(S.or(a, b)):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd(Tr(S.or(False{}, b)), false_ne_true(h))

def or_r(+a: Bool, +b: Bool, h: Tr(b)) -> Tr(S.or(a, b)):
  match a:
    case True{}:
      {==}
    case False{}:
      h

# or_elim picks the branch that holds. `c` is threaded to it, so a proof the
# branches both need is passed once instead of captured twice.
def or_elim(+a: Bool, +b: Bool, h: Tr(S.or(a, b)), -C: Type, c: C, -P: Type, kl: C -> Tr(a) -> P, kr: C -> Tr(b) -> P) -> P:
  match a:
    case True{}:
      kl(c, {==})
    case False{}:
      kr(c, h)

def and_intro(+a: Bool, +b: Bool, ha: Tr(a), hb: Tr(b)) -> Tr(S.and(a, b)):
  match a:
    case True{}:
      hb
    case False{}:
      Empty.absurd(Tr(S.and(False{}, b)), false_ne_true(ha))

def and_elim(+a: Bool, +b: Bool, h: Tr(S.and(a, b)), -C: Type, c: C, -P: Type, k: C -> Tr(a) -> Tr(b) -> P) -> P:
  match a:
    case True{}:
      k(c, {==}, h)
    case False{}:
      Empty.absurd(P, false_ne_true(h))

def edge_eq_refl(+e: S.Edge) -> Tr(S.edge_eq(e, e)):
  match e:
    case S.E{+a, +b}:
      and_intro(S.neq(a, a), S.neq(b, b), neq_refl(a), neq_refl(b))

def edge_eq_from(+a: Nat, +b: Nat, +c: Nat, +d: Nat, hac: Tr(S.neq(a, c)), hbd: Tr(S.neq(b, d))) -> {S.E{a, b} == S.E{c, d} : S.Edge}:
  ac = neq_sound(a, c, hac)
  bd = neq_sound(b, d, hbd)
  %bd : {S.E{a, b} == S.E{c, _} : S.Edge}
  %ac : {S.E{a, b} == S.E{_, b} : S.Edge}
  {==}

def edge_eq_sound(+x: S.Edge, +y: S.Edge, h: Tr(S.edge_eq(x, y))) -> {x == y : S.Edge}:
  match x y:
    case S.E{+a, +b} S.E{+c, +d}:
      and_elim(S.neq(a, c), S.neq(b, d), h, Unit, Unit{}, {S.E{a, b} == S.E{c, d} : S.Edge}, u => hac => hbd => edge_eq_from(a, b, c, d, hac, hbd))

# join_if_cons: when the join test holds, join_if is the cons.
def join_if_cons(+a: Nat, +d: Nat, +rest: S.Es, +hit: Bool, h: Tr(hit)) -> {S.ECons{S.E{a, d}, rest} == S.join_if(a, d, rest, hit) : S.Es}:
  match hit:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({S.ECons{S.E{a, d}, rest} == rest : S.Es}, false_ne_true(h))
