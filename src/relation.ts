/**
 * Fact is one stored tuple of term ids. A fact is never mutated; when an
 * `owl:sameAs` merge renames one of its terms it is retired (`diedAt`) and
 * the renamed tuple is stored as a new fact.
 */
export interface Fact {
  readonly args: readonly number[];
  readonly key: string;
  /** bornAt is the clock tick the fact was stored at. */
  readonly bornAt: number;
  /** diedAt is the tick the fact was retired at, or `Infinity` while live. */
  diedAt: number;
}

/** factKey renders the dedup key of a tuple. */
export function factKey(args: readonly number[]): string {
  return args.join(",");
}

const NO_FACTS: readonly Fact[] = [];

/**
 * Relation stores the facts of one predicate of fixed arity, with a hash index
 * per combination of bound columns. Single-column indexes exist from the
 * start, because a merge looks up every fact that mentions a renamed term;
 * wider indexes are built on first use and maintained from then on.
 *
 * Retired facts stay in {@link Relation.get} (so an incremental run can ask
 * what was live at an earlier tick) and are skipped lazily by lookups.
 */
export class Relation {
  readonly name: string;
  readonly arity: number;
  #facts = new Map<string, Fact>();
  #indexes = new Map<number, Map<IndexKey, Fact[]>>();
  #live = 0;

  constructor(name: string, arity: number) {
    this.name = name;
    this.arity = arity;
    for (let column = 0; column < arity; column++) {
      this.#indexes.set(1 << column, new Map());
    }
  }

  /** size is the number of live facts. */
  get size(): number {
    return this.#live;
  }

  /** get returns the fact stored under `key`, live or retired. */
  get(key: string): Fact | undefined {
    return this.#facts.get(key);
  }

  /** has is `true` when a live fact has exactly these args. */
  has(args: readonly number[]): boolean {
    const fact = this.#facts.get(factKey(args));
    return fact !== undefined && fact.diedAt === Infinity;
  }

  /**
   * insert stores `args` at tick `tick` and returns the new fact, or
   * `undefined` when a live fact already has these args.
   */
  insert(args: readonly number[], tick: number): Fact | undefined {
    const key = factKey(args);
    const existing = this.#facts.get(key);
    if (existing !== undefined && existing.diedAt === Infinity) {
      return undefined;
    }
    const fact: Fact = { args, key, bornAt: tick, diedAt: Infinity };
    this.#facts.set(key, fact);
    this.#live++;
    for (const [mask, index] of this.#indexes) {
      const indexKey = maskKey(mask, args);
      const bucket = index.get(indexKey);
      if (bucket === undefined) index.set(indexKey, [fact]);
      else bucket.push(fact);
    }
    return fact;
  }

  /** retire marks a live fact dead at tick `tick`. */
  retire(fact: Fact, tick: number): void {
    if (fact.diedAt !== Infinity) return;
    fact.diedAt = tick;
    this.#live--;
  }

  /**
   * lookup returns the facts whose columns in `mask` equal `values` (one value
   * per set bit, lowest column first). Retired facts may be included; callers
   * skip any fact whose `diedAt` is finite.
   */
  lookup(mask: number, values: readonly number[]): readonly Fact[] {
    if (mask === 0) return [...this.#facts.values()];
    if (values.length > 2) {
      // Look up on the two lowest bound columns, whose key packs into one
      // number; callers unify every fact, which checks the remaining columns.
      let narrowed = 0;
      for (let column = 0, kept = 0; kept < 2; column++) {
        if ((mask & (1 << column)) !== 0) {
          narrowed |= 1 << column;
          kept++;
        }
      }
      mask = narrowed;
      values = values.slice(0, 2);
    }
    let index = this.#indexes.get(mask);
    if (index === undefined) index = this.#buildIndex(mask);
    return index.get(valuesKey(values)) ?? NO_FACTS;
  }

  /** column returns the facts whose column `column` equals `id`. */
  column(column: number, id: number): readonly Fact[] {
    return this.#indexes.get(1 << column)!.get(id) ?? NO_FACTS;
  }

  /**
   * forget drops the single-column buckets of `id` once a merge has renamed
   * every fact in them, so the dead facts do not pin memory.
   */
  forget(id: number): void {
    for (let column = 0; column < this.arity; column++) {
      this.#indexes.get(1 << column)!.delete(id);
    }
  }

  /** facts yields every live fact. */
  *facts(): IterableIterator<Fact> {
    for (const fact of this.#facts.values()) {
      if (fact.diedAt === Infinity) yield fact;
    }
  }

  #buildIndex(mask: number): Map<IndexKey, Fact[]> {
    const index = new Map<IndexKey, Fact[]>();
    for (const fact of this.#facts.values()) {
      if (fact.diedAt !== Infinity) continue;
      const indexKey = maskKey(mask, fact.args);
      const bucket = index.get(indexKey);
      if (bucket === undefined) index.set(indexKey, [fact]);
      else bucket.push(fact);
    }
    this.#indexes.set(mask, index);
    return index;
  }
}

/**
 * IndexKey is an index bucket key: the bound value itself for one column, a
 * packed number for two (while ids stay below 2^26), a string beyond that.
 */
type IndexKey = number | string;

const PACK = 2 ** 26;

function valuesKey(values: readonly number[]): IndexKey {
  if (values.length === 1) return values[0]!;
  if (values.length === 2 && values[0]! < PACK && values[1]! < PACK) {
    return values[0]! * PACK + values[1]!;
  }
  return values.join(",");
}

function maskKey(mask: number, args: readonly number[]): IndexKey {
  const values: number[] = [];
  for (let column = 0; column < args.length; column++) {
    if ((mask & (1 << column)) !== 0) values.push(args[column]!);
  }
  return valuesKey(values);
}
