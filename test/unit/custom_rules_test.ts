import { assert, assertEquals, assertFalse, assertThrows } from "@std/assert";
import { dataFactory as df } from "@wazoo/sparql-engine/term";
import type { Quad } from "@rdfjs/types";
import { type CustomRule, Reasoner, variables } from "@/mod.ts";

const EX = "https://rules.example/";
const OWL_SAME_AS = "http://www.w3.org/2002/07/owl#sameAs";
const ex = (name: string) => df.namedNode(EX + name);
const triple = (s: string, p: string, o: string): Quad =>
  df.quad(ex(s), ex(p), ex(o));
const { x, y, z } = variables();

const grandparent: CustomRule = {
  name: "grandparent",
  body: [[x!, ex("parent"), y!], [y!, ex("parent"), z!]],
  head: [[x!, ex("grandparent"), z!]],
};

const keys = (quads: Iterable<Quad>) =>
  [...quads].map((q) =>
    `${q.subject.value} ${q.predicate.value} ${q.object.value}`
  )
    .sort();

Deno.test("custom rule derives triples from the constructor option", () => {
  const r = new Reasoner({ rules: [grandparent] });
  r.add([triple("a", "parent", "b"), triple("b", "parent", "c")]);
  r.run();
  assert(r.has(ex("a"), ex("grandparent"), ex("c")));
  assertFalse(r.has(ex("a"), ex("grandparent"), ex("b")));
});

Deno.test("custom rule chains with OWL 2 RL rules in one fixpoint", () => {
  const r = new Reasoner({
    rules: [grandparent, {
      name: "ancestor-of-grand",
      body: [[x!, ex("grandparent"), y!]],
      head: [[x!, ex("kin"), y!]],
    }],
  });
  r.add([
    triple("parent", "sub", "parent2"),
    df.quad(ex("parent"), df.namedNode(OWL_SAME_AS), ex("p2")),
    triple("a", "parent", "b"),
    triple("b", "p2", "c"),
  ]);
  r.run();
  // parent = p2 through sameAs, so a-parent-b, b-p2-c is a grandparent chain.
  assert(r.has(ex("a"), ex("grandparent"), ex("c")));
  assert(r.has(ex("a"), ex("kin"), ex("c")));
});

Deno.test("addRule applies to triples already added and run", () => {
  const r = new Reasoner();
  r.add([triple("a", "parent", "b"), triple("b", "parent", "c")]);
  r.run();
  assertFalse(r.has(ex("a"), ex("grandparent"), ex("c")));
  r.addRule(grandparent);
  assert(r.has(ex("a"), ex("grandparent"), ex("c")));
  assertEquals(r.rules.length, 1);
});

Deno.test("extend reports what custom rules newly derive", () => {
  const r = new Reasoner({ rules: [grandparent] });
  r.add([triple("a", "parent", "b")]);
  r.run();
  const added = r.extend([triple("b", "parent", "c")]);
  assertEquals(
    keys(added),
    keys([
      triple("b", "parent", "c"),
      triple("a", "grandparent", "c"),
    ]),
  );
});

Deno.test("retract with a custom rule equals a fresh run", () => {
  const base = [triple("a", "parent", "b"), triple("b", "parent", "c")];
  const r = new Reasoner({ rules: [grandparent] });
  r.add([...base, triple("c", "parent", "d")]);
  r.run();
  const removed = r.retract([triple("c", "parent", "d")]);
  assertEquals(
    keys(removed),
    keys([
      triple("c", "parent", "d"),
      triple("b", "grandparent", "d"),
    ]),
  );
  const fresh = new Reasoner({ rules: [grandparent] });
  fresh.add(base);
  fresh.run();
  assertEquals(keys(r.closure()), keys(fresh.closure()));
});

Deno.test("an inconsistent head reports the rule name and terms", () => {
  const r = new Reasoner({
    rules: [{
      name: "no-self-parent",
      body: [[x!, ex("parent"), x!]],
      inconsistent: [x!],
    }],
  });
  r.add([triple("a", "parent", "a")]);
  r.run();
  const found = r.inconsistencies();
  assertEquals(found.length, 1);
  assertEquals(found[0]!.rule, "no-self-parent");
  assertEquals(found[0]!.terms, [ex("a")]);
});

Deno.test("derived triples follow the closure view filters", () => {
  const r = new Reasoner({
    rules: [{
      name: "label-as-subject",
      body: [[x!, ex("name"), y!]],
      head: [[y!, ex("namedBy"), x!]],
    }],
  });
  r.add([df.quad(ex("a"), ex("name"), df.literal("A"))]);
  r.run();
  const literalSubject = (q: Quad) =>
    (q.subject.termType as string) === "Literal";
  assert([...r.closure("complete")].some(literalSubject));
  assertFalse([...r.closure("application")].some(literalSubject));
});

Deno.test("custom rules coexist with sameAs merging", () => {
  const r = new Reasoner({ rules: [grandparent] });
  r.add([
    triple("a", "parent", "b"),
    df.quad(ex("b"), df.namedNode(OWL_SAME_AS), ex("b2")),
    triple("b2", "parent", "c"),
  ]);
  r.run();
  assert(r.has(ex("a"), ex("grandparent"), ex("c")));
  assert(r.has(ex("a"), ex("grandparent"), ex("c")));
  r.retract([df.quad(ex("b"), df.namedNode(OWL_SAME_AS), ex("b2"))]);
  assertFalse(r.has(ex("a"), ex("grandparent"), ex("c")));
});

Deno.test("invalid rules are rejected with a clear error", () => {
  const r = new Reasoner();
  assertThrows(
    () =>
      r.addRule({
        name: "bad",
        body: [[x!, ex("p"), y!]],
        head: [[x!, ex("q"), z!]],
      }),
    Error,
    "unbound head variable ?z",
  );
  assertThrows(
    () =>
      r.addRule({
        name: "empty",
        body: [],
        head: [[ex("a"), ex("p"), ex("b")]],
      }),
    Error,
    "body needs at least one pattern",
  );
  assertThrows(
    () => r.addRule({ name: "nohead", body: [[x!, ex("p"), y!]] }),
    Error,
    "head pattern or an inconsistent",
  );
  assertThrows(
    () =>
      r.addRule({
        name: "cax-sco",
        body: [[x!, ex("p"), y!]],
        head: [[x!, ex("q"), y!]],
      }),
    Error,
    "OWL 2 RL rule name",
  );
  assertThrows(
    () =>
      r.addRule({
        name: "litpred",
        body: [[x!, ex("p"), y!]],
        head: [[x!, df.literal("p"), y!]],
      }),
    Error,
    "named node",
  );
  r.addRule(grandparent);
  assertThrows(() => r.addRule(grandparent), Error, "already registered");
  assertEquals(r.rules.length, 1);
});

Deno.test("extend sees a rule constant that is merged into another term", () => {
  // The rule names p1 and p2 as constants. Merging them makes the old fact
  // (a p1 b) match both atoms without being renamed, so extend must re-seed it.
  const clash: CustomRule = {
    name: "clash",
    body: [[x!, ex("p1"), y!], [x!, ex("p2"), y!]],
    inconsistent: [x!, y!],
  };
  const sameAs = (a: string, b: string) =>
    df.quad(ex(a), df.namedNode(OWL_SAME_AS), ex(b));
  for (const fact of ["p1", "p2"]) {
    for (const merge of [sameAs("p1", "p2"), sameAs("p2", "p1")]) {
      const reasoner = new Reasoner({ rules: [clash] });
      reasoner.add([triple("a", fact, "b")]);
      reasoner.run();
      assertEquals(reasoner.inconsistencies().length, 0);
      reasoner.extend([merge]);
      assertEquals(reasoner.inconsistencies().length, 1);
    }
  }
});

Deno.test("custom rules join across graphs and apply per graph", () => {
  const g1 = ex("g1");
  const g2 = ex("g2");
  const r = new Reasoner({ rules: [grandparent] });
  r.add([
    df.quad(ex("a"), ex("parent"), ex("b"), g1),
    df.quad(ex("b"), ex("parent"), ex("c"), g2),
  ]);
  r.run();
  // Entailment sees both graphs, so the derived triple exists; neither graph
  // entails it alone, so it is listed in the derived graph.
  assert(r.has(ex("a"), ex("grandparent"), ex("c")));
  assertFalse(r.has(ex("a"), ex("grandparent"), ex("c"), g1));
  // A rule added later reaches graphs whose closure is already computed.
  const late = new Reasoner();
  late.add([
    df.quad(ex("a"), ex("parent"), ex("b"), g1),
    df.quad(ex("b"), ex("parent"), ex("c"), g1),
    df.quad(ex("x"), ex("q"), ex("y"), g2),
  ]);
  late.run();
  late.addRule(grandparent);
  assert(late.has(ex("a"), ex("grandparent"), ex("c"), g1));
});
