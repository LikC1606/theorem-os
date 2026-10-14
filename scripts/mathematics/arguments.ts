import { parseArgs } from 'node:util';

export function parseFlags(argv: readonly string[], stringOptions: readonly string[]): Map<string, string> {
  const options = Object.fromEntries(stringOptions.map(name => [name, { type: 'string' as const }]));
  const { values, tokens } = parseArgs({ args: [...argv], options: { ...options, help: { type: 'boolean' } }, tokens: true });
  const seen = new Set<string>();
  for (const token of tokens) if (token.kind === 'option') {
    if (seen.has(token.name)) throw new Error(`Duplicate argument: --${token.name}`);
    seen.add(token.name);
  }
  return new Map(Object.entries(values).filter(([, value]) => value !== undefined).map(([key, value]) => [key, String(value)]));
}

export function required(flags: ReadonlyMap<string, string>, name: string): string {
  const value = flags.get(name)?.trim();
  if (!value) throw new Error(`--${name} is required`);
  return value;
}
