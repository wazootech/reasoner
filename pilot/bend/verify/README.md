# Bend verification pilot (reasoner#45)

Laws about `rdfs:subClassOf` transitivity (rule `scm-sco`), proved in Bend 2 and
checked twice: by `bend` and by its Lean-proved kernel (`--verdict`).

| File           | What it is                                                         |
| -------------- | ------------------------------------------------------------------ |
| `sco.bend`     | The code: edges, membership, and `step`, one naive round of scm-sco |
| `LAWS.bend`    | The claims, written by a human; each is an open `law`              |
| `PROOF.bend`   | One def per law; `bend PROOF.bend --verdict` is the gate           |
| `logic.bend`   | Lemmas about `Bool`, `Nat` equality and edge equality              |
| `mem.bend`     | Lemmas about membership and `append`                               |
| `compose.bend` | Lemmas about `compose`, the join that scm-sco is made of           |

## Run

Needs Bend 2.0.x, and for `--verdict` Lean v4.34.0 on the PATH (elan).

```sh
bend pilot/bend/verify/PROOF.bend --verdict   # ALL PROOFS CHECK
```

A pass means every law is proved for every input, not for sampled ones. The
checker is only as meaningful as the claims: a law that is too weak passes too,
so read `LAWS.bend`. Breaking `sco.bend` (a wrong join test, dropping the input
from `step`, a loose `neq`) makes the proofs fail, which is how this was tested.

Phase 12 compiles `sco.bend` with `bend -o x.mjs` for use as a test oracle.
