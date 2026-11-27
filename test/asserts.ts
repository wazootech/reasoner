/**
 * The few assertions the tests use, on `node:assert` so they run on Bun, Node
 * and Deno alike.
 */
import nodeAssert from "node:assert/strict";

// node:assert rejects an explicit `undefined` message, hence the branches.
export function assert(value: unknown, message?: string): asserts value {
  if (message === undefined) nodeAssert.ok(value);
  else nodeAssert.ok(value, message);
}

export function assertFalse(value: unknown, message?: string): void {
  assert(!value, message);
}

export function assertEquals<T>(
  actual: T,
  expected: T,
  message?: string,
): void {
  if (message === undefined) nodeAssert.deepStrictEqual(actual, expected);
  else nodeAssert.deepStrictEqual(actual, expected, message);
}

/** assertThrows checks the error's class and that its message has `includes`. */
export function assertThrows(
  run: () => unknown,
  errorClass: abstract new (...args: never[]) => Error = Error,
  includes = "",
): void {
  nodeAssert.throws(run, (error: unknown) => {
    nodeAssert.ok(error instanceof errorClass, `not a ${errorClass.name}`);
    nodeAssert.ok(error.message.includes(includes), error.message);
    return true;
  });
}
