import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { legacyEnvName } from "../common/config/legacyIdentifiers";

// Preserve the existing key identity so saved mathematical receipts remain valid.
export const MATH_RECEIPT_SECRET_ENV = 'DEEPSCIENTIST_FINANCE_RECEIPT_SECRET';
export const MATH_RECEIPT_KEY_PATH_ENV = 'DEEPSCIENTIST_FINANCE_RECEIPT_KEY_PATH';

export function resolveMathReceiptKeyPath(env: NodeJS.ProcessEnv = process.env): string {
  const explicit = env[MATH_RECEIPT_KEY_PATH_ENV]?.trim();
  if (explicit) return explicit;
  const isMultiInstance = env.DEEPSCIENTIST_MULTI_INSTANCE === '1' || env[legacyEnvName('MULTI_INSTANCE')] === '1';
  const environment = env.NODE_ENV === 'development' ? (isMultiInstance ? 'dev-2' : 'dev') : 'production';
  const identity = (
    env.VITEST
      ? `test-${process.pid}`
      : `${String(typeof process.getuid === 'function' ? process.getuid() : env.USERNAME || 'user')}-${environment}`
  ).replace(/[^a-zA-Z0-9_-]/g, '_').slice(0, 64);
  return path.join(os.tmpdir(), `deepscientist-finance-receipt-${identity}.key`);
}

export function readMathReceiptMasterSecret(env: NodeJS.ProcessEnv = process.env): string | undefined {
  const configured = env[MATH_RECEIPT_SECRET_ENV]?.trim();
  if (configured) return configured;
  const keyPath = resolveMathReceiptKeyPath(env);
  try {
    const existing = fs.readFileSync(keyPath, 'utf8').trim();
    if (existing) return existing;
  } catch {
    // Exclusive creation below also handles concurrent MCP startup.
  }
  if (env.DEEPSCIENTIST_MATH_ISOLATION_WORKSPACE) return undefined;
  const generated = crypto.randomBytes(32).toString('hex');
  try {
    fs.mkdirSync(path.dirname(keyPath), { recursive: true });
    const fd = fs.openSync(keyPath, 'wx', 0o600);
    try {
      fs.writeFileSync(fd, `${generated}\n`, 'utf8');
    } finally {
      fs.closeSync(fd);
    }
    return generated;
  } catch {
    try {
      return fs.readFileSync(keyPath, 'utf8').trim() || undefined;
    } catch {
      return undefined;
    }
  }
}
