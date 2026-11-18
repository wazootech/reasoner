# subset_pw turns a pointwise fact into the Bool `subset` test, which is what a
# loop invariant needs. The obstacle was that the pointwise proof uses a
# hypothesis, and Bend's functions can be used once. Here the hypothesis is a
# Bool equality `Tr(X(cx))`, which `dup` copies, and the pointwise function `g`
# is a template: substituted at each use, so it may be used many times, but it
# must be closed. It therefore takes its context `cx` (reusable data) as an
# argument instead of capturing it.
import Base
import ./sco.bend as S
import ./rl.bend as R
import ./logic.bend as L
import ./rl_mem.bend as RM
import ./rl_semi.bend as RS

def pw_cons(~Cx: Data, ~X: @+cx: Cx -> Bool, ~L0: @+cx: Cx -> R.Ts, ~T: @+cx: Cx -> R.Ts, ~g: @+cx: Cx -> @+c: R.Tri -> L.Tr(X(cx)) -> L.Tr(R.mem(c, L0(cx))) -> L.Tr(R.mem(c, T(cx))), +cx: Cx, +h: R.Tri, +tl: R.Ts, ea: L.Tr(X(cx)), hm: L.Tr(R.mem(h, L0(cx))), rec: L.Tr(R.subset(tl, T(cx)))) -> L.Tr(R.subset(R.TCons{h, tl}, T(cx))):
  L.and_intro(R.mem(h, T(cx)), R.subset(tl, T(cx)), g(cx, h, ea, hm), rec)

# subset_pw: every member of l is in L0(cx) (hs), and g puts every member of
# L0(cx) in T(cx) given X(cx). `e` carries two copies of the hypothesis.
def subset_pw(~Cx: Data, ~X: @+cx: Cx -> Bool, ~L0: @+cx: Cx -> R.Ts, ~T: @+cx: Cx -> R.Ts, ~g: @+cx: Cx -> @+c: R.Tri -> L.Tr(X(cx)) -> L.Tr(R.mem(c, L0(cx))) -> L.Tr(R.mem(c, T(cx))), +cx: Cx, +l: R.Ts, e: L.Tr(X(cx)) & L.Tr(X(cx)), hs: L.Tr(R.subset(l, L0(cx)))) -> L.Tr(R.subset(l, T(cx))):
  match l:
    case R.TNil{}:
      {==}
    case R.TCons{+h, +tl}:
      (ea, eb) = e
      L.and_elim(R.mem(h, L0(cx)), R.subset(tl, L0(cx)), hs, L.Tr(X(cx)), ea, L.Tr(R.subset(R.TCons{h, tl}, T(cx))),
        ea1 => hm => hst => pw_cons(~Cx, ~X, ~L0, ~T, ~g, cx, h, tl, ea1, hm,
          subset_pw(~Cx, ~X, ~L0, ~T, ~g, cx, tl, RS.dup(Bool, X(cx), True{}, eb), hst)))

# dup3 turns one equality proof into three copies, in one rewrite.
def dup3(-A: Type, -x: A, -y: A, h: {x == y : A}) -> {x == y : A} & ({x == y : A} & {x == y : A}):
  %h : ({x == _ : A} & ({x == _ : A} & {x == _ : A}))
  ({==}, ({==}, {==}))

def main() -> U32:
  1
