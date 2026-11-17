# Dedupe probe (reasoner#39)

The closure's unavoidable inner step is inserting derived triples into a
deduplicating set. Bend has no hash table, so its set is a tree. This probe
inserts the same 2.32M integer keys (8 chunks of 290,000 from one LCG; both
yield 1,783,170 distinct keys) into a 22-bit binary trie in Bend and into a JS
`Set`.

```sh
# WSL, Bend 2.0.39 + clang 18
bend trie.bend -o trie && ./trie +RTS --threads 8 -RTS
deno run trie_set.ts
```

The defs are `@unsafe` (no termination proofs), which does not change speed.
