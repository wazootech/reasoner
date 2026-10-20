/**
 * Literal value spaces for the OWL 2 RL datatype rules.
 *
 * The lexical checks and value comparisons are ported from Eyeling's `dt:`
 * builtins (MIT, Copyright 2025-2026 Jos De Roo, KNoWS office of IDLab, Ghent
 * University - imec), which back the ruleset the Wiki reasoned with before
 * this package, so a literal is valid, equal, or different here exactly when
 * it was there. One thing is deliberately narrower: Eyeling types a literal
 * with every datatype whose *lexical* space accepts its spelling, so
 * `"2026-01-01"^^xsd:date` became an `xsd:string` and an `xsd:anyURI`. Here a
 * literal is typed only within its own datatype's family
 * ({@link datatypeFamily}), because OWL 2 keeps those value spaces disjoint.
 */
import type { Literal } from "@rdfjs/types";
import { RDF_NS, RDFS_NS, XSD_NS } from "@/owl2rl/vocabulary.ts";

const RDF_LANGSTRING = RDF_NS + "langString";
const RDF_PLAIN_LITERAL = RDF_NS + "PlainLiteral";
const RDF_XML_LITERAL = RDF_NS + "XMLLiteral";
const RDFS_LITERAL = RDFS_NS + "Literal";
const XSD_STRING = XSD_NS + "string";
const XSD_BOOLEAN = XSD_NS + "boolean";
const XSD_DECIMAL = XSD_NS + "decimal";
const XSD_INTEGER = XSD_NS + "integer";
const XSD_FLOAT = XSD_NS + "float";
const XSD_DOUBLE = XSD_NS + "double";
const XSD_HEX_BINARY = XSD_NS + "hexBinary";
const XSD_BASE64_BINARY = XSD_NS + "base64Binary";
const XSD_ANY_URI = XSD_NS + "anyURI";
const XSD_DATETIME = XSD_NS + "dateTime";
const XSD_DATETIME_STAMP = XSD_NS + "dateTimeStamp";

const STRING_LIKE = new Set([
  XSD_STRING,
  XSD_NS + "normalizedString",
  XSD_NS + "token",
  XSD_NS + "language",
  XSD_NS + "Name",
  XSD_NS + "NCName",
  XSD_NS + "NMTOKEN",
]);

const INTEGER_BOUNDS = new Map<string, [bigint | null, bigint | null]>([
  [XSD_NS + "nonPositiveInteger", [null, 0n]],
  [XSD_NS + "negativeInteger", [null, -1n]],
  [XSD_NS + "long", [-(2n ** 63n), 2n ** 63n - 1n]],
  [XSD_NS + "int", [-(2n ** 31n), 2n ** 31n - 1n]],
  [XSD_NS + "short", [-(2n ** 15n), 2n ** 15n - 1n]],
  [XSD_NS + "byte", [-(2n ** 7n), 2n ** 7n - 1n]],
  [XSD_NS + "nonNegativeInteger", [0n, null]],
  [XSD_NS + "unsignedLong", [0n, 2n ** 64n - 1n]],
  [XSD_NS + "unsignedInt", [0n, 2n ** 32n - 1n]],
  [XSD_NS + "unsignedShort", [0n, 2n ** 16n - 1n]],
  [XSD_NS + "unsignedByte", [0n, 2n ** 8n - 1n]],
  [XSD_NS + "positiveInteger", [1n, null]],
]);

const SUPPORTED = new Set([
  RDF_LANGSTRING,
  RDF_PLAIN_LITERAL,
  RDF_XML_LITERAL,
  RDFS_LITERAL,
  ...STRING_LIKE,
  XSD_BOOLEAN,
  XSD_DECIMAL,
  XSD_INTEGER,
  XSD_FLOAT,
  XSD_DOUBLE,
  XSD_HEX_BINARY,
  XSD_BASE64_BINARY,
  XSD_ANY_URI,
  XSD_DATETIME,
  XSD_DATETIME_STAMP,
  ...INTEGER_BOUNDS.keys(),
]);

/** DatatypeValue is a literal's value, comparable within its family. */
export type DatatypeValue =
  | { family: "literal"; comparable: false }
  | { family: "string"; value: string; comparable: true }
  | {
    family: "langString" | "plainLiteral";
    value: string;
    lang: string;
    comparable: true;
  }
  | { family: "xmlLiteral" | "anyURI"; value: string; comparable: true }
  | { family: "boolean"; value: boolean; comparable: true }
  | { family: "binary"; bytes: number[]; comparable: true }
  | {
    family: "numeric";
    kind: "decimal";
    num: bigint;
    scale: number;
    comparable: true;
  }
  | { family: "numeric"; kind: "floating"; value: number; comparable: boolean }
  | {
    family: "dateTime";
    hasTimezone: boolean;
    totalSeconds: bigint;
    fracNum: bigint;
    fracScale: number;
    localKey: string;
    comparable: true;
  };

/** literalDatatype is the datatype IRI of `literal`, `rdf:langString` if tagged. */
export function literalDatatype(literal: Literal): string {
  if (literal.language) return RDF_LANGSTRING;
  return literal.datatype?.value ?? XSD_STRING;
}

/** isSupportedDatatype is `true` for a datatype OWL 2 RL's rules evaluate. */
export function isSupportedDatatype(datatype: string): boolean {
  return SUPPORTED.has(datatype);
}

/**
 * datatypeFamily names the value space a datatype's values live in; values of
 * different families are never equal, and a literal is only ever an instance
 * of datatypes in its own family (and of `rdfs:Literal`).
 */
export function datatypeFamily(datatype: string): string | undefined {
  if (!SUPPORTED.has(datatype)) return undefined;
  if (STRING_LIKE.has(datatype)) return "string";
  if (datatype === XSD_DECIMAL || datatype === XSD_INTEGER) return "decimal";
  if (INTEGER_BOUNDS.has(datatype)) return "decimal";
  if (datatype === XSD_DATETIME_STAMP) return XSD_DATETIME;
  return datatype;
}

/** literalValue parses `literal` in its own datatype, or `null` if ill-typed. */
export function literalValue(literal: Literal): DatatypeValue | null {
  return valueFor(literal, literalDatatype(literal));
}

/**
 * isInstanceOf is `true` when `literal` is a value of `datatype`: the two are
 * in one family and the literal's spelling is valid for `datatype`.
 */
export function isInstanceOf(literal: Literal, datatype: string): boolean {
  if (datatype !== RDFS_LITERAL) {
    const own = datatypeFamily(literalDatatype(literal));
    if (own === undefined || own !== datatypeFamily(datatype)) return false;
  }
  return valueFor(literal, datatype) !== null;
}

/** isInvalidFor is `true` for a supported `datatype` that `literal` is not in. */
export function isInvalidFor(literal: Literal, datatype: string): boolean {
  return isSupportedDatatype(datatype) && !isInstanceOf(literal, datatype);
}

/**
 * valuesDiffer is `true` when two literals have comparable values that are
 * not equal (Eyeling's `dt:differentValueFrom`).
 */
export function valuesDiffer(left: Literal, right: Literal): boolean {
  const a = literalValue(left);
  const b = literalValue(right);
  if (!comparable(a, b)) return false;
  return !sameValue(a!, b!);
}

function valueFor(literal: Literal, datatype: string): DatatypeValue | null {
  if (!SUPPORTED.has(datatype)) return null;
  if (datatype === RDFS_LITERAL) {
    const own = literalDatatype(literal);
    if (!SUPPORTED.has(own) || valueFor(literal, own) === null) return null;
    return { family: "literal", comparable: false };
  }
  const lexical = literal.value;
  if (datatype === RDF_LANGSTRING) {
    if (!literal.language || !isValidLanguageTag(literal.language, true)) {
      return null;
    }
    return {
      family: "langString",
      value: lexical,
      lang: literal.language.toLowerCase(),
      comparable: true,
    };
  }
  if (datatype === RDF_PLAIN_LITERAL) return plainLiteralValue(lexical);
  if (datatype === RDF_XML_LITERAL) {
    if (!isWellFormedXmlFragment(lexical)) return null;
    return { family: "xmlLiteral", value: lexical.trim(), comparable: true };
  }
  if (literal.language) return null;
  if (STRING_LIKE.has(datatype)) return stringValue(lexical, datatype);
  if (datatype === XSD_BOOLEAN) return booleanValue(lexical);
  if (datatype === XSD_INTEGER || INTEGER_BOUNDS.has(datatype)) {
    return integerValue(lexical, datatype);
  }
  if (datatype === XSD_DECIMAL) return decimalValue(lexical);
  if (datatype === XSD_FLOAT || datatype === XSD_DOUBLE) {
    return floatingValue(lexical, datatype);
  }
  if (datatype === XSD_HEX_BINARY || datatype === XSD_BASE64_BINARY) {
    return binaryValue(lexical, datatype);
  }
  if (datatype === XSD_ANY_URI) return anyUriValue(lexical);
  if (datatype === XSD_DATETIME || datatype === XSD_DATETIME_STAMP) {
    return dateTimeValue(lexical, datatype);
  }
  return null;
}

function comparable(a: DatatypeValue | null, b: DatatypeValue | null): boolean {
  if (!a || !b || !a.comparable || !b.comparable) return false;
  if (a.family === "dateTime" && b.family === "dateTime") {
    return a.hasTimezone === b.hasTimezone;
  }
  return a.family === b.family;
}

function sameValue(a: DatatypeValue, b: DatatypeValue): boolean {
  switch (a.family) {
    case "langString":
    case "plainLiteral":
      return b.family === a.family && a.value === b.value && a.lang === b.lang;
    case "string":
    case "xmlLiteral":
    case "anyURI":
    case "boolean":
      return b.family === a.family && a.value === (b as typeof a).value;
    case "binary": {
      if (b.family !== "binary" || a.bytes.length !== b.bytes.length) {
        return false;
      }
      return a.bytes.every((byte, index) => byte === b.bytes[index]);
    }
    case "numeric": {
      if (b.family !== "numeric") return false;
      if (a.kind === "decimal" && b.kind === "decimal") {
        const scale = Math.max(a.scale, b.scale);
        return a.num * 10n ** BigInt(scale - a.scale) ===
          b.num * 10n ** BigInt(scale - b.scale);
      }
      const left = a.kind === "decimal"
        ? Number(a.num) / 10 ** a.scale
        : a.value;
      const right = b.kind === "decimal"
        ? Number(b.num) / 10 ** b.scale
        : b.value;
      return !Number.isNaN(left) && !Number.isNaN(right) && left === right;
    }
    case "dateTime": {
      if (b.family !== "dateTime" || a.hasTimezone !== b.hasTimezone) {
        return false;
      }
      if (!a.hasTimezone) return a.localKey === b.localKey;
      if (a.totalSeconds !== b.totalSeconds) return false;
      const scale = Math.max(a.fracScale, b.fracScale);
      return a.fracNum * 10n ** BigInt(scale - a.fracScale) ===
        b.fracNum * 10n ** BigInt(scale - b.fracScale);
    }
    default:
      return false;
  }
}

function isValidLanguageTag(tag: string, allowDirection: boolean): boolean {
  const pattern = allowDirection
    ? /^[A-Za-z]{1,8}(?:-[A-Za-z0-9]{1,8})*(?:--(?:ltr|rtl))?$/
    : /^[A-Za-z]{1,8}(?:-[A-Za-z0-9]{1,8})*$/;
  return pattern.test(tag);
}

function plainLiteralValue(lexical: string): DatatypeValue | null {
  const at = lexical.lastIndexOf("@");
  if (at < 0) return null;
  const lang = lexical.slice(at + 1);
  if (lang !== "" && !isValidLanguageTag(lang, false)) return null;
  return {
    family: "plainLiteral",
    value: lexical.slice(0, at),
    lang: lang.toLowerCase(),
    comparable: true,
  };
}

function stringValue(lexical: string, datatype: string): DatatypeValue | null {
  if (datatype === XSD_NS + "normalizedString") {
    if (/[\t\n\r]/.test(lexical)) return null;
  } else if (datatype !== XSD_STRING) {
    // Collapsed-whitespace datatypes accept only already-collapsed spellings.
    if (
      /[\t\n\r]/.test(lexical) || /^ | $/.test(lexical) || / {2,}/.test(lexical)
    ) {
      return null;
    }
  }
  if (datatype === XSD_NS + "language") {
    if (!isValidLanguageTag(lexical, false)) return null;
  } else if (datatype === XSD_NS + "Name") {
    if (!/^[:_\p{L}][:_\p{L}\p{N}.\-·̀-ͯ‿-⁀]*$/u.test(lexical)) {
      return null;
    }
  } else if (datatype === XSD_NS + "NCName") {
    if (!/^[_\p{L}][_\p{L}\p{N}.\-·̀-ͯ‿-⁀]*$/u.test(lexical)) {
      return null;
    }
  } else if (datatype === XSD_NS + "NMTOKEN") {
    if (!/^[:_\p{L}\p{N}.\-·̀-ͯ‿-⁀]+$/u.test(lexical)) {
      return null;
    }
  }
  const value = datatype === XSD_NS + "language"
    ? lexical.toLowerCase()
    : lexical;
  return { family: "string", value, comparable: true };
}

function booleanValue(lexical: string): DatatypeValue | null {
  if (lexical === "true" || lexical === "1") {
    return { family: "boolean", value: true, comparable: true };
  }
  if (lexical === "false" || lexical === "0") {
    return { family: "boolean", value: false, comparable: true };
  }
  return null;
}

function integerValue(lexical: string, datatype: string): DatatypeValue | null {
  if (!/^[+-]?\d+$/.test(lexical)) return null;
  const value = BigInt(lexical);
  const bounds = INTEGER_BOUNDS.get(datatype);
  if (bounds) {
    const [min, max] = bounds;
    if (min !== null && value < min) return null;
    if (max !== null && value > max) return null;
  }
  return {
    family: "numeric",
    kind: "decimal",
    num: value,
    scale: 0,
    comparable: true,
  };
}

function decimalValue(lexical: string): DatatypeValue | null {
  let text = lexical;
  let sign = 1n;
  if (text.startsWith("+")) text = text.slice(1);
  else if (text.startsWith("-")) {
    sign = -1n;
    text = text.slice(1);
  }
  if (!/^(?:\d+(?:\.\d*)?|\.\d+)$/.test(text)) return null;
  let [whole = "0", fraction = ""] = text.split(".");
  if (whole === "") whole = "0";
  whole = whole.replace(/^0+(?=\d)/, "");
  fraction = fraction.replace(/0+$/, "");
  return {
    family: "numeric",
    kind: "decimal",
    num: sign * BigInt(whole + fraction || "0"),
    scale: fraction.length,
    comparable: true,
  };
}

const FLOAT_MAX = 3.4028234663852886e38;
const FLOAT_MIN_POSITIVE = 1.401298464324817e-45;

function floatingValue(
  lexical: string,
  datatype: string,
): DatatypeValue | null {
  const special = lexical === "INF" || lexical === "+INF"
    ? Infinity
    : lexical === "-INF"
    ? -Infinity
    : lexical === "NaN"
    ? NaN
    : null;
  if (
    special === null &&
    !/^[+-]?(?:(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?|\d+(?:[eE][+-]?\d+))$/
      .test(lexical)
  ) {
    return null;
  }
  const value = special ?? Number(lexical);
  if (Number.isFinite(value)) {
    const magnitude = Math.abs(value);
    const [max, min] = datatype === XSD_FLOAT
      ? [FLOAT_MAX, FLOAT_MIN_POSITIVE]
      : [Number.MAX_VALUE, Number.MIN_VALUE];
    if (magnitude > 0 && (magnitude > max || magnitude < min)) return null;
  }
  return {
    family: "numeric",
    kind: "floating",
    value,
    comparable: !Number.isNaN(value),
  };
}

const BASE64 =
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

function binaryValue(lexical: string, datatype: string): DatatypeValue | null {
  if (datatype === XSD_HEX_BINARY) {
    if (!/^(?:[0-9A-Fa-f]{2})*$/.test(lexical)) return null;
    const bytes: number[] = [];
    for (let index = 0; index < lexical.length; index += 2) {
      bytes.push(parseInt(lexical.slice(index, index + 2), 16));
    }
    return { family: "binary", bytes, comparable: true };
  }
  const text = lexical.replace(/[\t\n\r ]+/g, "");
  if (text.length === 0) {
    return { family: "binary", bytes: [], comparable: true };
  }
  if (text.length % 4 !== 0 || !/^[A-Za-z0-9+/]*={0,2}$/.test(text)) {
    return null;
  }
  const pad = text.endsWith("==") ? 2 : text.endsWith("=") ? 1 : 0;
  if (pad && text.slice(0, -pad).includes("=")) return null;
  const bytes: number[] = [];
  for (let index = 0; index < text.length; index += 4) {
    const codes = [0, 1, 2, 3].map((offset) => {
      const char = text[index + offset]!;
      return char === "=" ? 0 : BASE64.indexOf(char);
    });
    if (codes.some((code) => code < 0)) return null;
    const n = (codes[0]! << 18) | (codes[1]! << 12) | (codes[2]! << 6) |
      codes[3]!;
    bytes.push((n >> 16) & 0xff);
    if (text[index + 2] !== "=") bytes.push((n >> 8) & 0xff);
    if (text[index + 3] !== "=") bytes.push(n & 0xff);
  }
  return { family: "binary", bytes, comparable: true };
}

function anyUriValue(lexical: string): DatatypeValue | null {
  if (/[^!-~]/.test(lexical) || /[<>"{}|\\^`]/.test(lexical)) {
    return null;
  }
  for (let index = 0; index < lexical.length; index++) {
    if (
      lexical[index] === "%" &&
      !/^[0-9A-Fa-f]{2}$/.test(lexical.slice(index + 1, index + 3))
    ) {
      return null;
    }
  }
  // A relative reference may not start with a colon-bearing path segment.
  if (
    lexical !== "" && !/^[A-Za-z][A-Za-z0-9+.-]*:/.test(lexical) &&
    !/^[/?#]/.test(lexical)
  ) {
    const cut = lexical.search(/[/?#]/);
    if ((cut < 0 ? lexical : lexical.slice(0, cut)).includes(":")) return null;
  }
  return { family: "anyURI", value: lexical, comparable: true };
}

function isWellFormedXmlFragment(input: string): boolean {
  const source = input.trim();
  if (!source) return false;
  const stack: string[] = [];
  let seenElement = false;
  let position = 0;
  while (position < source.length) {
    const open = source.indexOf("<", position);
    if (open < 0) {
      return stack.length === 0 && isValidXmlText(source.slice(position)) &&
        seenElement;
    }
    if (!isValidXmlText(source.slice(position, open))) return false;
    const skip = (start: string, end: string): boolean => {
      if (!source.startsWith(start, open)) return false;
      const close = source.indexOf(end, open + start.length);
      if (close < 0) throw new SyntaxError("unterminated");
      if (start === "<!--" && source.slice(open + 4, close).includes("--")) {
        throw new SyntaxError("double hyphen");
      }
      position = close + end.length;
      return true;
    };
    try {
      if (skip("<!--", "-->") || skip("<![CDATA[", "]]>") || skip("<?", "?>")) {
        continue;
      }
    } catch {
      return false;
    }
    if (source.startsWith("</", open)) {
      const close = source.indexOf(">", open + 2);
      if (close < 0) return false;
      const name = source.slice(open + 2, close).trim();
      if (!isValidXmlName(name) || stack.pop() !== name) return false;
      position = close + 1;
      continue;
    }
    const close = findXmlTagEnd(source, open + 1);
    if (close < 0) return false;
    const raw = source.slice(open + 1, close);
    const selfClosing = /\/\s*$/.test(raw);
    const content = selfClosing ? raw.replace(/\/\s*$/, "").trim() : raw.trim();
    const name = /^([^\s/>]+)/.exec(content);
    if (
      !name || !isValidXmlName(name[1]!) ||
      !areValidXmlAttributes(content.slice(name[0].length))
    ) {
      return false;
    }
    seenElement = true;
    if (!selfClosing) stack.push(name[1]!);
    position = close + 1;
  }
  return stack.length === 0 && seenElement;
}

function findXmlTagEnd(source: string, start: number): number {
  let quote: string | null = null;
  for (let index = start; index < source.length; index++) {
    const char = source[index]!;
    if (quote) {
      if (char === quote) quote = null;
    } else if (char === '"' || char === "'") {
      quote = char;
    } else if (char === ">") {
      return index;
    }
  }
  return -1;
}

function areValidXmlAttributes(source: string): boolean {
  let rest = source.trim();
  const seen = new Set<string>();
  while (rest) {
    const match =
      /^([A-Za-z_:\u0080-￿][A-Za-z0-9_.:\-\u0080-￿]*)\s*=\s*("[^"]*"|'[^']*')\s*/u
        .exec(rest);
    if (!match || seen.has(match[1]!)) return false;
    const value = match[2]!.slice(1, -1);
    if (/</.test(value) || !isValidXmlText(value)) return false;
    seen.add(match[1]!);
    rest = rest.slice(match[0].length).trim();
  }
  return true;
}

function isValidXmlText(value: string): boolean {
  return !/[<&]/.test(
    value.replace(/&(?:amp|lt|gt|quot|apos|#\d+|#x[0-9A-Fa-f]+);/g, ""),
  );
}

function isValidXmlName(name: string): boolean {
  return /^[A-Za-z_:\u0080-￿][A-Za-z0-9_.:\-\u0080-￿]*$/u.test(name) &&
    !/^xml$/i.test(name);
}

function isLeapYear(year: bigint): boolean {
  if (year % 400n === 0n) return true;
  if (year % 100n === 0n) return false;
  return year % 4n === 0n;
}

function daysInMonth(year: bigint, month: number): number {
  if (month === 2) return isLeapYear(year) ? 29 : 28;
  return [4, 6, 9, 11].includes(month) ? 30 : 31;
}

function floorDiv(a: bigint, b: bigint): bigint {
  let quotient = a / b;
  const remainder = a % b;
  if (remainder !== 0n && (remainder > 0n) !== (b > 0n)) quotient -= 1n;
  return quotient;
}

function daysFromCivil(year: bigint, month: number, day: number): bigint {
  const y = month <= 2 ? year - 1n : year;
  const era = floorDiv(y, 400n);
  const yearOfEra = y - era * 400n;
  const shifted = BigInt(month + (month > 2 ? -3 : 9));
  const dayOfYear = (153n * shifted + 2n) / 5n + BigInt(day) - 1n;
  const dayOfEra = yearOfEra * 365n + yearOfEra / 4n - yearOfEra / 100n +
    dayOfYear;
  return era * 146097n + dayOfEra - 719468n;
}

function civilFromDays(
  days: bigint,
): { year: bigint; month: number; day: number } {
  const z = days + 719468n;
  const era = floorDiv(z, 146097n);
  const dayOfEra = z - era * 146097n;
  const yearOfEra =
    (dayOfEra - dayOfEra / 1460n + dayOfEra / 36524n - dayOfEra / 146096n) /
    365n;
  let year = yearOfEra + era * 400n;
  const dayOfYear = dayOfEra -
    (365n * yearOfEra + yearOfEra / 4n - yearOfEra / 100n);
  const shifted = (5n * dayOfYear + 2n) / 153n;
  const day = dayOfYear - (153n * shifted + 2n) / 5n + 1n;
  const month = shifted < 10n ? shifted + 3n : shifted - 9n;
  if (month <= 2n) year += 1n;
  return { year, month: Number(month), day: Number(day) };
}

function localKey(
  year: bigint,
  month: number,
  day: number,
  hour: number,
  minute: number,
  second: number,
  fraction: string,
): string {
  const yearText = year < 0n
    ? `-${(-year).toString().padStart(4, "0")}`
    : year.toString().padStart(4, "0");
  const pad = (value: number) => String(value).padStart(2, "0");
  return `${yearText}-${pad(month)}-${pad(day)}T${pad(hour)}:${pad(minute)}:${
    pad(second)
  }${fraction ? `.${fraction}` : ""}`;
}

function dateTimeValue(
  lexical: string,
  datatype: string,
): DatatypeValue | null {
  const match =
    /^(-?\d{4,})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(?:\.(\d+))?(Z|[+-]\d{2}:\d{2})?$/
      .exec(lexical);
  if (!match) return null;
  const yearDigits = match[1]!.replace(/^-/, "");
  if (yearDigits.length !== 4 && yearDigits[0] === "0") return null;
  let year = BigInt(match[1]!);
  let month = Number(match[2]);
  let day = Number(match[3]);
  let hour = Number(match[4]);
  const minute = Number(match[5]);
  const second = Number(match[6]);
  let fraction = match[7] ?? "";
  const zone = match[8] ?? null;
  if (datatype === XSD_DATETIME_STAMP && !zone) return null;
  if (month < 1 || month > 12) return null;
  if (day < 1 || day > daysInMonth(year, month)) return null;
  if (minute > 59 || second > 59) return null;
  let dayCount = daysFromCivil(year, month, day);
  if (hour === 24) {
    if (minute !== 0 || second !== 0 || /[1-9]/.test(fraction)) return null;
    hour = 0;
    dayCount += 1n;
    ({ year, month, day } = civilFromDays(dayCount));
  } else if (hour > 23) {
    return null;
  }
  fraction = fraction.replace(/0+$/g, "");
  let offsetMinutes: number | null = null;
  if (zone === "Z") offsetMinutes = 0;
  else if (zone) {
    const hours = Number(zone.slice(1, 3));
    const minutes = Number(zone.slice(4, 6));
    if (hours > 14 || minutes > 59 || (hours === 14 && minutes !== 0)) {
      return null;
    }
    offsetMinutes = (zone[0] === "-" ? -1 : 1) * (hours * 60 + minutes);
  }
  let totalSeconds = dayCount * 86400n +
    BigInt(hour * 3600 + minute * 60 + second);
  if (offsetMinutes !== null) totalSeconds -= BigInt(offsetMinutes * 60);
  return {
    family: "dateTime",
    hasTimezone: offsetMinutes !== null,
    totalSeconds,
    fracNum: fraction ? BigInt(fraction) : 0n,
    fracScale: fraction.length,
    localKey: localKey(year, month, day, hour, minute, second, fraction),
    comparable: true,
  };
}
