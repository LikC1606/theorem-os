import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {
  afterEach,
  describe,
  expect,
  it,
  vi,
} from 'vitest';
import {
  MATH_RECEIPT_KEY_PATH_ENV,
  MATH_RECEIPT_SECRET_ENV,
  readMathReceiptMasterSecret,
  resolveMathReceiptKeyPath,
} from '../src/math/receiptKey';
import { readMathematicsReceiptSecret, signMathOfficialGateReceipt } from '../src/math/receiptAttestation';

const roots: string[] = [];
const keyFile = () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-receipt-key-'));
  roots.push(root);
  return path.join(root, 'receipt.key');
};
afterEach(() => {
  vi.unstubAllEnvs();
  for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true });
});

describe('mathematical receipt key compatibility', () => {
  it('preserves historical receipt signatures after sharing canonical JSON', () => {
    const receipt = signMathOfficialGateReceipt({
      receiptId: ' fixture-legacy ', targetCommit: 'a'.repeat(40), statementHash: 'B'.repeat(64),
      claim: 'negation', routeFingerprint: ' Test  Route ', localGateReceiptId: 'fixture-local',
      theoremName: 'Example.goal', proofHash: 'c'.repeat(64), theoremDeclarationHash: 'd'.repeat(64),
      sourceDeclarationHash: 'e'.repeat(64), status: 'official_verified', verifier: 'official-comparator',
      command: 'lean Submission.lean', exitCode: 0, timedOut: false,
      stdoutSha256: 'f'.repeat(64), stderrSha256: '0'.repeat(64), durationMs: 12, checkedAt: 1760000000000,
      problemId: 'fixture-problem', officialManifestPath: '.math/manifest.json',
      officialManifestId: 'fixture-manifest', officialManifestHash: '1'.repeat(64),
      leanStatementHash: '2'.repeat(64), officialRepositoryUrl: 'https://example.invalid/fixture.git',
      officialBaselineCommit: 'b'.repeat(40), benchmarkAdapterId: 'fixture-adapter', benchmarkAdapterVersion: '1',
    }, 'fixture-compatibility-secret');
    // Captured with the original signer, using only this synthetic receipt and key.
    expect(receipt.attestation).toEqual({
      algorithm: 'hmac-sha256', keyId: 'b28845a55cd48baa',
      value: 'c17d2bb8c965713fe9082213560c1a668602bbd20bee5770edb7bca8c076ac96',
    });
  });

  it('keeps historical production, development and test key paths', () => {
    const uid = String(process.getuid?.() ?? 'user');
    expect(resolveMathReceiptKeyPath({})).toBe(path.join(os.tmpdir(), `deepscientist-finance-receipt-${uid}-production.key`));
    expect(resolveMathReceiptKeyPath({ NODE_ENV: 'development' })).toContain(`${uid}-dev.key`);
    expect(resolveMathReceiptKeyPath({ NODE_ENV: 'development', DEEPSCIENTIST_MULTI_INSTANCE: '1' })).toContain(`${uid}-dev-2.key`);
    expect(resolveMathReceiptKeyPath({ NODE_ENV: 'development', AIONUI_MULTI_INSTANCE: '1' })).toContain(`${uid}-dev-2.key`);
    expect(resolveMathReceiptKeyPath({ VITEST: 'true' })).toContain(`test-${process.pid}.key`);
    expect(resolveMathReceiptKeyPath({ [MATH_RECEIPT_KEY_PATH_ENV]: ' /explicit/key ' })).toBe('/explicit/key');
  });

  it('creates a private key once and reuses it', () => {
    const file = keyFile();
    const env = { [MATH_RECEIPT_KEY_PATH_ENV]: file };
    const key = readMathReceiptMasterSecret(env);
    expect(key).toMatch(/^[a-f0-9]{64}$/);
    expect(fs.statSync(file).mode & 0o777).toBe(0o600);
    expect(readMathReceiptMasterSecret(env)).toBe(key);
  });

  it('uses an explicit secret without creating a file', () => {
    const file = keyFile();
    expect(readMathReceiptMasterSecret({ [MATH_RECEIPT_KEY_PATH_ENV]: file, [MATH_RECEIPT_SECRET_ENV]: ' existing-secret ' })).toBe('existing-secret');
    expect(fs.existsSync(file)).toBe(false);
  });

  it('requires the host key inside an isolated workspace', () => {
    const file = keyFile();
    const env = { [MATH_RECEIPT_KEY_PATH_ENV]: file, DEEPSCIENTIST_MATH_ISOLATION_WORKSPACE: '/isolated' };
    expect(readMathReceiptMasterSecret(env)).toBeUndefined();
    expect(fs.existsSync(file)).toBe(false);
    fs.writeFileSync(file, 'mounted-host-key\n');
    expect(readMathReceiptMasterSecret(env)).toBe('mounted-host-key');
  });

  it('derives the same mathematical signing key from an existing master key', () => {
    const file = keyFile();
    fs.writeFileSync(file, 'existing-host-key\n');
    vi.stubEnv(MATH_RECEIPT_SECRET_ENV, '');
    vi.stubEnv(MATH_RECEIPT_KEY_PATH_ENV, file);
    expect(readMathematicsReceiptSecret()).toBe(crypto.createHmac('sha256', 'existing-host-key')
      .update('deepscientist.mathematics.receipt-key.v1').digest('hex'));
  });
});
