import type { Term } from "@rdfjs/types";
import { termKey } from "@wazoo/sparql-engine/term";

/**
 * TermDictionary interns RDF/JS terms as small integers, so facts are arrays
 * of numbers and every index key is a short string of digits. Ids are dense
 * and never reused; an id stays valid for the dictionary's lifetime.
 */
export class TermDictionary {
  #ids = new Map<string, number>();
  #terms: Term[] = [];

  /** id returns the id of `term`, interning it first if it is new. */
  id(term: Term): number {
    const key = termKey(term);
    let id = this.#ids.get(key);
    if (id === undefined) {
      id = this.#terms.length;
      this.#ids.set(key, id);
      this.#terms.push(term);
    }
    return id;
  }

  /** lookup returns the id of `term`, or `undefined` if it was never interned. */
  lookup(term: Term): number | undefined {
    return this.#ids.get(termKey(term));
  }

  /** term returns the term interned as `id`. */
  term(id: number): Term {
    const term = this.#terms[id];
    if (term === undefined) throw new RangeError(`Unknown term id ${id}`);
    return term;
  }

  /** size is the number of interned terms. */
  get size(): number {
    return this.#terms.length;
  }
}
