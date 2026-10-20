import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { expect, it } from 'vitest';
import { leanStatementContextCommands, parseLeanStatementContexts } from '../src/math/leanStatementContext';
import { runLeanProcess } from '../src/math/mathProcess';

it('preserves the exact default context generator while allowing an explicit known-bound omission', () => {
  const roots = [{ id: '__ID__', name: '__ROOT__' }], modules = [{ module: '__MODULE__', file: '__FILE__' }];
  const legacy = leanStatementContextCommands(roots, modules, '__CONTEXT__');
  expect(crypto.createHash('sha256').update(legacy).digest('hex'))
    .toBe('1f86ef6b6b8dac30ac5f7cff87d45d4d2450c4c18f8e9b8bca03cf2e071f34f3');
  expect(leanStatementContextCommands(roots, modules, '__CONTEXT__', { omitOversizedType: false })).toBe(legacy);
  const optional = leanStatementContextCommands(roots, modules, '__CONTEXT__', { omitOversizedType: true });
  expect(optional).toContain('"statement-type-export-bound"');
  expect(optional).not.toContain('then throwError "Statement type exceeds its export bound"');
});

it('keeps known-bound failure reports invalid for the ordinary statement-context parser', () => {
  expect(() => parseLeanStatementContexts(JSON.stringify([{ id: 'wide', context: {
    unavailable: 'statement-type-export-bound', bytes: 24001, limit: 24000,
  } }]), ['wide'])).toThrow('math_statement_elaboration_invalid');
});

const lean = path.join(os.homedir(), '.elan', 'toolchains', 'leanprover--lean4---v4.33.0', 'bin', 'lean');
it.skipIf(!fs.existsSync(lean))('omits only oversized types per root while preserving ordinary contexts and propagating other Lean errors', async () => {
  const directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'statement-bound-')));
  try {
    const binder = 'long_' + 'n'.repeat(500), source =
      `theorem longReadable (${binder} : Nat) : ${Array(30).fill(`(${binder} = ${binder})`).join(' ∧ ')} := by simp\n` +
      'theorem small : True := True.intro\n';
    fs.writeFileSync(path.join(directory, 'Submission.lean'), source);
    const input = { cwd: directory, env: { ...process.env, LEAN_PATH: directory }, timeoutMs: Infinity, outputLimit: 1_000_000 };
    const built = await runLeanProcess(lean, ['-o', 'Submission.olean', 'Submission.lean'], input);
    expect(built.exitCode, built.stdout + built.stderr).toBe(0);
    const modules = [{ module: 'Submission', file: 'Submission.lean' }];
    const query = async (file: string, roots: { id: string; name: string }[], output: string, omitOversizedType?: boolean) => {
      fs.writeFileSync(path.join(directory, file), 'import Lean\nimport Submission\n' +
        leanStatementContextCommands(roots, modules, output, { omitOversizedType }) + '\n');
      return runLeanProcess(lean, ['--json', file], input);
    };
    const defaultResult = await query('Default.lean', [{ id: 'wide', name: 'longReadable' }], 'default.json');
    expect(defaultResult.exitCode).not.toBe(0);
    expect(defaultResult.stdout).toContain('Statement type exceeds its export bound');
    expect(fs.existsSync(path.join(directory, 'default.json'))).toBe(false);

    const enabled = await query('Optional.lean', [{ id: 'wide', name: 'longReadable' }, { id: 'small', name: 'small' }], 'optional.json', true);
    expect(enabled.exitCode, enabled.stdout + enabled.stderr).toBe(0);
    const [wide, small] = JSON.parse(fs.readFileSync(path.join(directory, 'optional.json'), 'utf8'));
    expect(wide).toEqual({ id: 'wide', context: { unavailable: 'statement-type-export-bound', bytes: expect.any(Number), limit: 24000 } });
    expect(wide.context.bytes).toBeGreaterThan(24000);
    expect(parseLeanStatementContexts(JSON.stringify([small]), ['small']).get('small')?.type).toBe('True');
    expect(() => parseLeanStatementContexts(JSON.stringify([wide]), ['wide'])).toThrow('math_statement_elaboration_invalid');

    const normal = await query('Small.lean', [{ id: 'small', name: 'small' }], 'small.json');
    expect(normal.exitCode, normal.stdout + normal.stderr).toBe(0);
    expect(JSON.parse(fs.readFileSync(path.join(directory, 'small.json'), 'utf8'))).toEqual([small]);

    const missing = await query('Missing.lean', [{ id: 'missing', name: 'missingRoot' }], 'missing.json', true);
    expect(missing.exitCode).not.toBe(0); expect(missing.stdout).toContain('missingRoot');
    expect(fs.existsSync(path.join(directory, 'missing.json'))).toBe(false);
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
}, 30000);
