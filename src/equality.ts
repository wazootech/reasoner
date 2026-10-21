/**
 * Equality keeps `owl:sameAs` as a union-find over term ids instead of as
 * copied triples, the way RDFox does: every stored fact names only class
 * representatives, and the materialized closure is the product of each
 * fact's term classes.
 *
 * Union is by size and finds do not compress paths, so the tree depth stays
 * logarithmic and every link keeps the clock tick it was made at. That makes
 * the state at any earlier tick recoverable ({@link Equality.findAt}), which
 * is how an incremental run tells a triple it newly entails from one that was
 * already in the closure before a merge.
 */
export class Equality {
  #parent: number[] = [];
  #size: number[] = [];
  #linkedAt: number[] = [];
  #members = new Map<number, number[]>();

  #grow(id: number): void {
    for (let next = this.#parent.length; next <= id; next++) {
      this.#parent.push(next);
      this.#size.push(1);
      this.#linkedAt.push(Infinity);
    }
  }

  /** find returns the representative of the class holding `id`. */
  find(id: number): number {
    const parent = this.#parent;
    if (id >= parent.length) return id;
    while (parent[id] !== id) id = parent[id]!;
    return id;
  }

  /** findAt returns the representative `id` had before clock tick `tick`. */
  findAt(id: number, tick: number): number {
    const parent = this.#parent;
    if (id >= parent.length) return id;
    while (parent[id] !== id && this.#linkedAt[id]! < tick) id = parent[id]!;
    return id;
  }

  /**
   * union merges the classes of `a` and `b` at clock tick `tick`, and returns
   * the representative that was absorbed, or `undefined` if they were already
   * one class.
   */
  union(a: number, b: number, tick: number): number | undefined {
    this.#grow(Math.max(a, b));
    let root = this.find(a);
    let absorbed = this.find(b);
    if (root === absorbed) return undefined;
    // Larger class wins; on a tie the smaller id, so runs are deterministic.
    if (
      this.#size[absorbed]! > this.#size[root]! ||
      (this.#size[absorbed] === this.#size[root] && absorbed < root)
    ) {
      [root, absorbed] = [absorbed, root];
    }
    this.#parent[absorbed] = root;
    this.#linkedAt[absorbed] = tick;
    this.#size[root] = this.#size[root]! + this.#size[absorbed]!;
    const kept = this.#members.get(root) ?? [root];
    const moved = this.#members.get(absorbed) ?? [absorbed];
    for (const member of moved) kept.push(member);
    this.#members.set(root, kept);
    this.#members.delete(absorbed);
    return absorbed;
  }

  /** members returns every id in the class whose representative is `root`. */
  members(root: number): readonly number[] {
    return this.#members.get(root) ?? [root];
  }

  /** isTrivial is `true` when `root` is alone in its class. */
  isTrivial(root: number): boolean {
    return !this.#members.has(root);
  }

  /** rootsChangedSince returns the roots of every class merged at or after `tick`. */
  rootsChangedSince(tick: number): Set<number> {
    const roots = new Set<number>();
    for (let id = 0; id < this.#parent.length; id++) {
      if (this.#linkedAt[id]! >= tick && this.#linkedAt[id] !== Infinity) {
        roots.add(this.find(id));
      }
    }
    return roots;
  }

  /** classes yields the representative of every class with two or more members. */
  classes(): IterableIterator<number> {
    return this.#members.keys();
  }
}
