import type { LeanDiagnosticMessage } from './leanTypes';

const position = (value: unknown): value is number => typeof value === 'number' && Number.isSafeInteger(value) && value >= 0;
const goalText = (message: string) => /(?:^|\n)unsolved goals\n([\s\S]+)/u.exec(message)?.[1];

function rawMessages(output: string): LeanDiagnosticMessage[] {
  return output.split(/(?=^.+:\d+:\d+:\s*(?:error|warning|info)(?:\([^\n)]*\))?:)/mu).flatMap(block => {
    const header = /^(.+):(\d+):(\d+):\s*(error|warning|info)(?:\(([^\n)]*)\))?:\s*([\s\S]*)/u.exec(block);
    if (!header) return [];
    const message = header[6].trimEnd();
    return [{ format: 'raw' as const, file: header[1], line: Number(header[2]), column: Math.max(0, Number(header[3]) - 1),
      severity: header[4] as LeanDiagnosticMessage['severity'], message, ...(header[5] ? { code: header[5] } : {}),
      ...(goalText(message) ? { goalText: goalText(message) } : {}) }];
  });
}

/** Read Lean's --json messages, retaining unsupported output as raw fallback. */
export function parseLeanDiagnosticOutput(output: string) {
  const messages: LeanDiagnosticMessage[] = [], raw: string[] = [];
  let pending: string[] = [];
  const flush = () => { messages.push(...rawMessages(pending.join('\n'))); pending = []; };
  for (const line of output.split('\n')) {
    if (!line.trim()) { raw.push(line); pending.push(line); continue; }
    let value: any;
    try { value = JSON.parse(line); } catch { /* Older Lean or non-message process output. */ }
    if (value && typeof value === 'object' && !Array.isArray(value) && typeof value.data === 'string' &&
        ['error', 'warning', 'info'].includes(value.severity)) {
      flush();
      messages.push({ format: 'lean-json', severity: value.severity, message: value.data,
        ...(typeof value.fileName === 'string' ? { file: value.fileName } : {}),
        ...(position(value.pos?.line) && position(value.pos?.column) ? { line: value.pos.line, column: value.pos.column } : {}),
        ...(position(value.endPos?.line) && position(value.endPos?.column) ? { endLine: value.endPos.line, endColumn: value.endPos.column } : {}),
        ...(typeof value.kind === 'string' && value.kind !== '[anonymous]' ? { code: value.kind } : {}),
        ...(goalText(value.data) ? { goalText: goalText(value.data) } : {}) });
    } else { raw.push(line); pending.push(line); }
  }
  flush();
  const fallback = raw.join('\n');
  return { messages, raw: fallback };
}

export function renderLeanDiagnosticMessage(message: LeanDiagnosticMessage) {
  const location = message.file ? `${message.file}${message.line === undefined ? '' : `:${message.line}:${(message.column ?? 0) + 1}`}: ` : '';
  return `${location}${message.severity}${message.code ? `(${message.code})` : ''}: ${message.message}`;
}

export function renderLeanDiagnosticOutput(output: string) {
  const parsed = parseLeanDiagnosticOutput(output);
  const json = parsed.messages.filter(message => message.format === 'lean-json').map(renderLeanDiagnosticMessage).join('\n');
  return [json, parsed.raw].filter(Boolean).join('\n');
}
