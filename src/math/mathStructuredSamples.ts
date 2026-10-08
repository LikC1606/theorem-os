import { createHash } from 'node:crypto';

export type MathStructuredSampleDesign = Readonly<{
  kind: 'integer_list' | 'rational_grid' | 'finite_graph' | 'finite_operation';
  count: number;
  seed: string;
  min?: number;
  max?: number;
  maxLength?: number;
  denominatorMax?: number;
  vertices?: number;
  carrierSize?: number;
}>;

function integer(value: number | undefined, name: string, minimum: number, maximum = Number.MAX_SAFE_INTEGER): number {
  if (!Number.isSafeInteger(value) || value! < minimum || value! > maximum)
    throw new TypeError(`Invalid sample ${name}`);
  return value!;
}

function power(base: bigint, exponent: number): bigint {
  let result = BigInt(1);
  for (let index = 0; index < exponent; index++) result *= base;
  return result;
}

/** Enumerate a finite structured domain by rank, then sample ranks reproducibly. */
export function generateStructuredMathSamples(design: MathStructuredSampleDesign): readonly string[] {
  integer(design.count, 'count', 1, 16);
  if (!design.seed || design.seed.length > 512) throw new TypeError('Invalid sample seed');
  let size: bigint;
  let render: (rank: bigint) => string;
  if (design.kind === 'integer_list') {
    const min = integer(design.min, 'min', Number.MIN_SAFE_INTEGER);
    const max = integer(design.max, 'max', min);
    const length = integer(design.maxLength, 'maxLength', 0, 64);
    const width = BigInt(max) - BigInt(min) + BigInt(1);
    size = Array.from({ length: length + 1 }, (_, n) => power(width, n)).reduce((a, b) => a + b, BigInt(0));
    render = (rank) => {
      let n = 0;
      while (rank >= power(width, n)) rank -= power(width, n++);
      const values = Array.from({ length: n }, () => {
        const value = BigInt(min) + (rank % width);
        rank /= width;
        return String(value);
      });
      return `([${values.join(', ')}] : List Int)`;
    };
  } else if (design.kind === 'rational_grid') {
    const min = integer(design.min, 'min', Number.MIN_SAFE_INTEGER);
    const max = integer(design.max, 'max', min);
    const denominator = integer(design.denominatorMax, 'denominatorMax', 1);
    const width = BigInt(max) - BigInt(min) + BigInt(1);
    size = width * BigInt(denominator);
    render = (rank) => `((${BigInt(min) + (rank % width)} : Rat) / ${BigInt(1) + rank / width})`;
  } else if (design.kind === 'finite_graph') {
    const vertices = integer(design.vertices, 'vertices', 0, 32);
    const edges: [number, number][] = [];
    for (let a = 0; a < vertices; a++) for (let b = a + 1; b < vertices; b++) edges.push([a, b]);
    size = BigInt(1) << BigInt(edges.length);
    render = (rank) =>
      `([${edges
        .filter((_, i) => (rank & (BigInt(1) << BigInt(i))) !== BigInt(0))
        .map(([a, b]) => `(${a}, ${b})`)
        .join(', ')}] : List (Prod Nat Nat))`;
  } else if (design.kind === 'finite_operation') {
    const carrier = integer(design.carrierSize, 'carrierSize', 1, 16);
    size = power(BigInt(carrier), carrier * carrier);
    render = (rank) => {
      const rows = Array.from(
        { length: carrier },
        () =>
          `[${Array.from({ length: carrier }, () => {
            const value = rank % BigInt(carrier);
            rank /= BigInt(carrier);
            return String(value);
          }).join(', ')}]`
      );
      return `([${rows.join(', ')}] : List (List Nat))`;
    };
  } else throw new TypeError('Unknown structured sample design');
  if (BigInt(design.count) > size) throw new TypeError('Sample count exceeds the finite domain');
  const ranks = new Set<bigint>([BigInt(0)]);
  if (design.count > 1) ranks.add(size - BigInt(1));
  for (let index = 0; ranks.size < design.count; index++) {
    const blocks = Math.ceil(size.toString(2).length / 256);
    const expanded = Array.from({ length: blocks }, (_, block) =>
      createHash('sha256')
        .update(JSON.stringify([design.seed, index, block]))
        .digest('hex')
    ).join('');
    let rank = BigInt(`0x${expanded}`) % size;
    while (ranks.has(rank)) rank = (rank + BigInt(1)) % size;
    ranks.add(rank);
  }
  return Object.freeze([...ranks].map(render));
}

export function shrinkMathProbeSample(value: string): readonly string[] {
  const unique = (items: readonly string[]) =>
    Object.freeze([...new Set(items)].filter((item) => item !== value).slice(0, 16));
  const smallerIntegers = (n: bigint) =>
    [...new Set([BigInt(0), n / BigInt(2), n > BigInt(0) ? n - BigInt(1) : n + BigInt(1)])].filter(
      (candidate) => candidate * candidate < n * n
    );
  if (/^-?\d+$/u.test(value)) {
    const n = BigInt(value);
    return unique(smallerIntegers(n).map(String));
  }
  const rational = /^\(\((-?\d+) : Rat\) \/ (\d+)\)$/u.exec(value);
  if (rational && BigInt(rational[2]!) > BigInt(0)) {
    const numerator = BigInt(rational[1]!);
    const denominator = BigInt(rational[2]!);
    const render = (n: bigint, d: bigint) => `((${n} : Rat) / ${d})`;
    return unique([
      ...smallerIntegers(numerator).map((n) => render(n, denominator)),
      ...smallerIntegers(denominator)
        .filter((d) => d > BigInt(0))
        .map((d) => render(numerator, d)),
      ...(denominator > BigInt(1) ? [render(numerator, BigInt(1))] : []),
    ]);
  }
  const graph = /^\(\[(.*)\] : List \(Prod Nat Nat\)\)$/u.exec(value);
  if (graph && /^(?:\s*\(\d+,\s*\d+\)\s*(?:,\s*\(\d+,\s*\d+\)\s*)*)?$/u.test(graph[1]!)) {
    const edges = [...graph[1]!.matchAll(/\((\d+),\s*(\d+)\)/gu)].map(
      (match) => [Number(match[1]), Number(match[2])] as const
    );
    if (edges.some(([a, b]) => !Number.isSafeInteger(a) || !Number.isSafeInteger(b) || a >= b)) return [];
    const render = (items: typeof edges) =>
      `([${items.map(([a, b]) => `(${a}, ${b})`).join(', ')}] : List (Prod Nat Nat))`;
    return unique(
      [
        [],
        edges.slice(0, Math.floor(edges.length / 2)),
        edges.slice(Math.ceil(edges.length / 2)),
        ...edges.map((_, index) => edges.filter((__, i) => i !== index)),
      ].map(render)
    );
  }
  const operation = /^\((\[.*\]) : List \(List Nat\)\)$/u.exec(value);
  if (operation) {
    let rows: unknown;
    try {
      rows = JSON.parse(operation[1]!);
    } catch {
      return [];
    }
    if (
      !Array.isArray(rows) ||
      !rows.length ||
      !rows.every(
        (row) =>
          Array.isArray(row) &&
          row.length === rows.length &&
          row.every((n) => Number.isSafeInteger(n) && n >= 0 && n < rows.length)
      )
    )
      return [];
    const table = rows as number[][];
    const render = (items: number[][]) =>
      `([${items.map((row) => `[${row.join(', ')}]`).join(', ')}] : List (List Nat))`;
    return unique([
      ...(table.length > 1
        ? [render([[0]]), render(table.slice(0, -1).map((row) => row.slice(0, -1).map((n) => n % (table.length - 1))))]
        : []),
      render(table.map((row) => row.map(() => 0))),
      render(table.map((row) => row.map((n) => Math.floor(n / 2)))),
      ...table.flatMap((row, i) =>
        row.flatMap((n, j) =>
          n === 0 ? [] : [render(table.map((r, a) => r.map((v, b) => (a === i && b === j ? 0 : v))))]
        )
      ),
    ]);
  }
  if (value.startsWith('([') && value.endsWith('] : List Int)')) {
    let values: unknown;
    try {
      values = JSON.parse(value.slice(1, -12));
    } catch {
      return [];
    }
    if (!Array.isArray(values) || !values.every(Number.isSafeInteger)) return [];
    const integers = values as number[];
    const render = (items: number[]) => `([${items.join(', ')}] : List Int)`;
    return unique(
      [
        [],
        values.slice(0, Math.floor(values.length / 2)),
        integers.map(() => 0),
        integers.map((n) => Math.trunc(n / 2)),
        ...values.map((_, i) => values.filter((__, j) => i !== j)),
        ...integers.flatMap((n, i) =>
          smallerIntegers(BigInt(n)).map((v) => integers.map((entry, j) => (i === j ? Number(v) : entry)))
        ),
      ].map(render)
    );
  }
  return [];
}
