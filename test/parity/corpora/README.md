# Parity corpora

Asserted graphs (before inference), dumped to N-Triples the way the Wiki CLI
loads them. `deno task test:parity` runs every `.nt` file here.

| File            | Source                                                                    |
| --------------- | ------------------------------------------------------------------------- |
| `docs.nt`       | The Wiki's own documentation site (`wazootech/wiki`, `docs/wiki.yml`)     |
| `micro.nt`      | The Wiki's micro OWL 2 RL fixture (`tests/fixtures/micro/wiki.yml`)       |
| `owl.nt`        | A synthetic ontology exercising every OWL 2 RL rule family, with `sameAs` |
| `owl-nosame.nt` | The same ontology with every `owl:sameAs` producer removed                |
| `bench-1e3.nt`  | The `bench:shacl` fixture at 10³ quads (wazootech/wiki#416)               |

The private `memory` corpus and the 10⁴ bench fixture are checked locally by
passing their paths: `deno task test:parity path/to/memory.nt`.
