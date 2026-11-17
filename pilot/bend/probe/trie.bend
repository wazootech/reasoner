import Base

type Trie is Data:
  TNil{}
  TLeaf{}
  TNode{lo: Trie, hi: Trie}

@unsafe def insert(+d: Nat, t: Trie, +k: U32) -> Trie:
  match d:
    case 0n:
      TLeaf{}
    case 1n+p:
      b = U32.is_eq(((k >> p) .&. 1 : U32), 1)
      step(b, p, t, k)

@unsafe def step(b: Bool, +p: Nat, t: Trie, +k: U32) -> Trie:
  match b t:
    case True{} TNode{lo, hi}:
      TNode{lo, insert(p, hi, k)}
    case False{} TNode{lo, hi}:
      TNode{insert(p, lo, k), hi}
    case True{} _:
      TNode{TNil{}, insert(p, TNil{}, k)}
    case False{} _:
      TNode{insert(p, TNil{}, k), TNil{}}

@unsafe def fill(z: Bool, n: U32, t: Trie, s: U32) -> Trie:
  match z:
    case True{}:
      t
    case False{}:
      +s2 = (s * 1664525 + 1013904223 : U32)
      k = ((s2 >> 8n) .&. 4194303 : U32)
      +m = (n - 1 : U32)
      fill(U32.is_eq(m, 0), m, insert(22n, t, k), s2)

@unsafe def union(a: Trie, b: Trie) -> Trie:
  match a b:
    case TNode{al, ah} TNode{bl, bh}:
      l h = union(al, bl) union(ah, bh)
      TNode{l, h}
    case TNil{} y:
      y
    case x TNil{}:
      x
    case x _:
      x

@unsafe def build(+s: Nat, +seed: U32, +chunk: U32) -> Trie:
  match s:
    case 0n:
      fill(U32.is_eq(chunk, 0), chunk, TNil{}, seed)
    case 1n+p:
      a b = build(p, (seed * 2 + 1 : U32), chunk) build(p, (seed * 2 + 2 : U32), chunk)
      union(a, b)

@unsafe def count(t: Trie) -> U32:
  match t:
    case TNil{}:
      0
    case TLeaf{}:
      1
    case TNode{lo, hi}:
      a b = count(lo) count(hi)
      (a + b : U32)

def report(t0: Nat, +t1: Nat, t2: Nat, n: U32) -> IO(Unit):
  IO.print("distinct=" ++ U32.show(n) ++ " build_ms=" ++ Nat.show(Nat.sub(t1, t0)) ++ " count_ms=" ++ Nat.show(Nat.sub(t2, t1)))

def main() -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    t : Trie = build(3n, 1, 290000)
    +t1 : Nat <- IO.now()
    n : U32 = count(t)
    +t2 : Nat <- IO.now()
    report(t0, t1, t2, n)
