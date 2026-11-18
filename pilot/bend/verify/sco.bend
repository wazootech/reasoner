# rdfs:subClassOf transitivity (scm-sco) over edge lists: the code the laws in
# LAWS.bend are about. Classes are `Nat` ids. A graph is a list of edges, with
# duplicates allowed: the laws are about membership, so the list is a set.
import Base

type Edge is Data:
  E{a: Nat, b: Nat}

type Es is Data:
  ENil{}
  ECons{h: Edge, t: Es}

# neq is `Nat` equality by structural recursion, so proofs can unfold it.
def neq(+a: Nat, +b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+bp:
      False{}
    case 1n+ap 0n:
      False{}
    case 1n+ap 1n+bp:
      neq(ap, bp)

def or(+a: Bool, +b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

def and(+a: Bool, +b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

def edge_eq(+x: Edge, +y: Edge) -> Bool:
  match x y:
    case E{+a, +b} E{+c, +d}:
      and(neq(a, c), neq(b, d))

def mem(+e: Edge, +es: Es) -> Bool:
  match es:
    case ENil{}:
      False{}
    case ECons{+h, +t}:
      or(edge_eq(e, h), mem(e, t))

def append(+xs: Es, +ys: Es) -> Es:
  match xs:
    case ENil{}:
      ys
    case ECons{+h, +t}:
      ECons{h, append(t, ys)}

# join_if adds (a, d) in front of `rest` when the middle ids b and c match.
def join_if(+a: Nat, +d: Nat, +rest: Es, +hit: Bool) -> Es:
  match hit:
    case True{}:
      ECons{E{a, d}, rest}
    case False{}:
      rest

# compose1 is every (a, d) with (c, d) in `es` and c equal to the edge's b.
def compose1(+e: Edge, +es: Es) -> Es:
  match e es:
    case E{+a, +b} ENil{}:
      ENil{}
    case E{+a, +b} ECons{E{+c, +d}, +t}:
      join_if(a, d, compose1(E{a, b}, t), neq(b, c))

def compose(+xs: Es, +ys: Es) -> Es:
  match xs:
    case ENil{}:
      ENil{}
    case ECons{+h, +t}:
      append(compose1(h, ys), compose(t, ys))

# insert_if adds e in front of es unless `hit` says it is already there. It is
# its own def because Bend cannot match on a computed value.
def insert_if(+hit: Bool, +e: Edge, +es: Es) -> Es:
  match hit:
    case True{}:
      es
    case False{}:
      ECons{e, es}

def insert(+e: Edge, +es: Es) -> Es:
  insert_if(mem(e, es), e, es)

# union inserts every edge of xs into base, so base never gains a duplicate.
def union(+xs: Es, +base: Es) -> Es:
  match xs:
    case ENil{}:
      base
    case ECons{+h, +t}:
      union(t, insert(h, base))

# step is one round of scm-sco: the graph plus every composed edge it lacks.
def step(+es: Es) -> Es:
  union(compose(es, es), es)

# subset is the loop's stop test: every edge of xs is in ys.
def subset(+xs: Es, +ys: Es) -> Bool:
  match xs:
    case ENil{}:
      True{}
    case ECons{+h, +t}:
      and(mem(h, ys), subset(t, ys))

# iter runs n rounds of step. Whether n rounds are enough is not proved here:
# the caller checks `subset(step(r), r)` on the result instead.
def iter(+n: Nat, +es: Es) -> Es:
  match n:
    case 0n:
      es
    case 1n+p:
      step(iter(p, es))

def main() -> Es:
  # 0 -> 1 -> 2 -> 3 gives 0 -> 2, 1 -> 3 and 0 -> 3 over two rounds.
  g : Es = ECons{E{0n, 1n}, ECons{E{1n, 2n}, ECons{E{2n, 3n}, ENil{}}}}
  iter(2n, g)
