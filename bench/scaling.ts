/**
 * Scaling benchmark: closure time and memory for seeded synthetic graphs of
 * growing size, with and without `owl:sameAs` producers.
 *
 *     deno task bench [--sizes 1e3,1e4,1e5,1e6]
 *                     [--profile plain|equality|sameas] [--check]
 *
 * With `--check` the run fails when a time is over its limit in
 * `bench/thresholds.json`, or when doubling the size more than
 * `maxDoublingRatio`-folds the time (the shape of the quadratic bug in #5).
 * The limits are several times the measured baseline, because CI machines vary.
 *
 * `plain` exercises the class and property rules (subclasses, domains and
 * ranges, inverses, a transitive chain). `equality` adds a functional and an
 * inverse-functional property, so about 1% of people collapse into
 * `owl:sameAs` classes: the case that was quadratic before. `sameas` is the
 * repro from #5: every person has two values on a functional property (so the
 * values merge), and half the people are explicitly `owl:sameAs` the previous
 * one.
 */
import { parseArgs } from "@std/cli/parse-args";
import type { Quad } from "@rdfjs/types";
import { dataFactory } from "@wazoo/sparql-engine/term";
import { Reasoner } from "@/mod.ts";

const EX = "https://bench.example/";
const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
const OWL = "http://www.w3.org/2002/07/owl#";
const XSD = "http://www.w3.org/2001/XMLSchema#";

const node = (iri: string) => dataFactory.namedNode(iri);
const ex = (name: string) => node(EX + name);

function mulberry32(seed: number): () => number {
  return () => {
    seed = (seed + 0x6d2b79f5) | 0;
    let value = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    value = (value + Math.imul(value ^ (value >>> 7), 61 | value)) ^ value;
    return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
  };
}

export type Profile = "plain" | "equality" | "sameas";

/** sameAsHeavy is the repro of #5: about `size` asserted triples. */
function sameAsHeavy(size: number): Quad[] {
  const quad = (s: string, p: string, o: string) =>
    dataFactory.quad(ex(s), node(p), node(o));
  const quads = [quad("hasId", RDF_TYPE, `${OWL}FunctionalProperty`)];
  for (let i = 0; i * 4 < size; i++) {
    quads.push(quad(`p${i}`, RDF_TYPE, `${EX}Person`));
    quads.push(quad(`p${i}`, `${EX}hasId`, `${EX}v${i}`));
    quads.push(quad(`p${i}`, `${EX}hasId`, `${EX}w${i}`));
    quads.push(
      i > 0 && i % 2 === 0
        ? quad(`p${i}`, `${OWL}sameAs`, `${EX}p${i - 1}`)
        : quad(`p${i}`, `${EX}knows`, `${EX}p${i + 1}`),
    );
  }
  return quads;
}

/** generate returns about `size` asserted triples for `profile`. */
export function generate(size: number, profile: Profile): Quad[] {
  if (profile === "sameas") return sameAsHeavy(size);
  const random = mulberry32(size);
  const quads: Quad[] = [];
  const add = (s: string, p: string, o: Quad["object"]) =>
    quads.push(dataFactory.quad(ex(s), node(p), o));
  const axiom = (s: string, p: string, o: string) => add(s, p, node(o));
  axiom("Employee", `${RDFS}subClassOf`, `${EX}Person`);
  axiom("Manager", `${RDFS}subClassOf`, `${EX}Employee`);
  axiom("Person", `${RDFS}subClassOf`, `${EX}Agent`);
  axiom("Company", `${RDFS}subClassOf`, `${EX}Organization`);
  axiom("worksFor", `${RDFS}domain`, `${EX}Employee`);
  axiom("worksFor", `${RDFS}range`, `${EX}Company`);
  axiom("worksFor", `${OWL}inverseOf`, `${EX}employs`);
  axiom("reportsTo", `${RDF_TYPE}`, `${OWL}TransitiveProperty`);
  axiom("knows", `${RDF_TYPE}`, `${OWL}SymmetricProperty`);
  axiom("name", `${RDF_TYPE}`, `${OWL}DatatypeProperty`);
  if (profile === "equality") {
    axiom("taxId", `${RDF_TYPE}`, `${OWL}InverseFunctionalProperty`);
    axiom("spouse", `${RDF_TYPE}`, `${OWL}FunctionalProperty`);
  }
  // Each person contributes about five triples.
  const people = Math.max(10, Math.floor(size / 5));
  const companies = Math.max(1, Math.floor(people / 50));
  for (let index = 0; index < people; index++) {
    const person = `p${index}`;
    add(person, RDF_TYPE, ex(random() < 0.1 ? "Manager" : "Employee"));
    add(person, `${EX}worksFor`, ex(`c${Math.floor(random() * companies)}`));
    add(person, `${EX}name`, dataFactory.literal(`Person ${index}`));
    // A manager chain of depth up to ten keeps the transitive closure linear.
    if (index % 10 !== 0) add(person, `${EX}reportsTo`, ex(`p${index - 1}`));
    add(person, `${EX}knows`, ex(`p${Math.floor(random() * people)}`));
    if (profile === "equality") {
      // One person in a hundred shares a tax id with the previous person.
      const taxId = random() < 0.01 && index > 0 ? index - 1 : index;
      add(
        person,
        `${EX}taxId`,
        dataFactory.literal(String(taxId), node(`${XSD}integer`)),
      );
    }
  }
  return quads;
}

function peakRssMb(): number | undefined {
  try {
    const status = Deno.readTextFileSync("/proc/self/status");
    const match = /VmHWM:\s+(\d+) kB/.exec(status);
    if (match) return Math.round(Number(match[1]) / 1024);
  } catch {
    // Not Linux; fall back to the current RSS.
  }
  return Math.round(Deno.memoryUsage().rss / 1024 / 1024);
}

interface Thresholds {
  /** maxDoublingRatio is the most a doubled size may multiply the time. */
  maxDoublingRatio: number;
  /** Per profile, the most milliseconds a run of that many triples may take. */
  profiles: Record<string, Record<string, number>>;
}

if (import.meta.main) {
  const args = parseArgs(Deno.args, {
    string: ["sizes", "profile"],
    boolean: ["check"],
    default: { sizes: "1e3,1e4,1e5", profile: "plain" },
  });
  const sizes = args.sizes.split(",").map(Number);
  const profile = args.profile as Profile;
  const thresholds: Thresholds = JSON.parse(
    Deno.readTextFileSync(new URL("./thresholds.json", import.meta.url)),
  );
  const failures: string[] = [];
  let previous: { size: number; ms: number } | undefined;
  console.log(
    "| Asserted | Profile | Closure | Merges | Rounds | Time | ms / 1k triples | RSS |",
  );
  console.log("|---:|---|---:|---:|---:|---:|---:|---:|");
  for (const size of sizes) {
    const quads = generate(size, profile);
    const start = performance.now();
    const reasoner = new Reasoner();
    reasoner.add(quads);
    reasoner.run();
    let closure = 0;
    for (const _ of reasoner.closure("application")) closure++;
    const ms = performance.now() - start;
    const stats = reasoner.statistics;
    console.log(
      `| ${quads.length} | ${profile} | ${closure} | ${stats.merges} | ${stats.rounds} | ` +
        `${(ms / 1000).toFixed(2)} s | ${
          (ms / (quads.length / 1000)).toFixed(1)
        } | ` +
        `${peakRssMb()} MB |`,
    );
    const limit = thresholds.profiles[profile]?.[String(size)];
    if (limit !== undefined && ms > limit) {
      failures.push(`${profile} ${size}: ${Math.round(ms)} ms > ${limit} ms`);
    }
    // Ignore sub-100 ms baselines: the ratio of two tiny times is noise.
    if (
      previous !== undefined && size === previous.size * 2 &&
      previous.ms >= 100 && ms / previous.ms > thresholds.maxDoublingRatio
    ) {
      failures.push(
        `${profile} ${previous.size} -> ${size}: x${
          (ms / previous.ms).toFixed(1)
        } per doubling > x${thresholds.maxDoublingRatio}`,
      );
    }
    previous = { size, ms };
  }
  if (failures.length > 0) {
    console.error(`\nBenchmark regressions:\n  ${failures.join("\n  ")}`);
    if (args.check) Deno.exit(1);
  }
}
