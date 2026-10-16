import path from 'node:path';
import { z } from 'zod';
import { getLeanTaskEnvironment } from '../../src/math/leanTaskEnvironment';
import type { WebEnvironment, WebEnvironmentOption, WebProvider, WebTemplate } from './shared';

const providerSchema = z.object({
  id: z.string().regex(/^[a-z][a-z0-9-]{0,39}$/),
  name: z.string().trim().min(1).max(80),
  baseUrl: z.string().url().max(512),
}).strict();

export type WebConfig = {
  host: string;
  port: number;
  publicUrl: string;
  staticRoot: string;
  workerImage: string;
  concurrency: number;
  queueLimit: number;
  sessionTtlMs: number;
  providers: WebProvider[];
};

function integer(value: string | undefined, fallback: number, min: number, max: number): number {
  const parsed = value === undefined ? fallback : Number(value);
  if (!Number.isInteger(parsed) || parsed < min || parsed > max) throw new Error('Invalid web service limit.');
  return parsed;
}

export function readWebConfig(env: NodeJS.ProcessEnv = process.env): WebConfig {
  const port = integer(env.THEOREMOS_WEB_PORT, 8787, 1, 65535);
  const publicUrl = new URL(env.THEOREMOS_WEB_PUBLIC_URL || `http://127.0.0.1:${port}`);
  if (!['http:', 'https:'].includes(publicUrl.protocol) || publicUrl.pathname !== '/' || publicUrl.search ||
      publicUrl.hash || publicUrl.username || publicUrl.password) throw new Error('Use an HTTP(S) origin for THEOREMOS_WEB_PUBLIC_URL.');
  const providers = z.array(providerSchema).min(1).max(20).parse(JSON.parse(env.THEOREMOS_WEB_PROVIDERS ||
    '[{"id":"openai","name":"OpenAI","baseUrl":"https://api.openai.com/v1"}]')) as WebProvider[];
  if (new Set(providers.map(provider => provider.id)).size !== providers.length) throw new Error('Provider IDs must be unique.');
  for (const provider of providers) {
    const url = new URL(provider.baseUrl);
    if (url.protocol !== 'https:' || url.username || url.password || url.search || url.hash)
      throw new Error('Provider base URLs must use HTTPS without credentials, queries or fragments.');
    provider.baseUrl = url.href.replace(/\/$/, '');
  }
  return {
    host: env.THEOREMOS_WEB_HOST || '127.0.0.1', port, publicUrl: publicUrl.origin,
    staticRoot: path.resolve(env.THEOREMOS_WEB_STATIC_ROOT || 'out/web'),
    workerImage: env.THEOREMOS_WEB_WORKER_IMAGE || 'theorem-os-worker:local',
    concurrency: integer(env.THEOREMOS_WEB_CONCURRENCY, 1, 1, 8),
    queueLimit: integer(env.THEOREMOS_WEB_QUEUE_LIMIT, 8, 1, 32),
    sessionTtlMs: 60 * 60 * 1000, providers,
  };
}

export const webLimits = Object.freeze({ maxTurns: 20, maxRunSeconds: 900, maxWorkers: 4,
  maxSourceBytes: 32_768, maxTaskBytes: 8_000 });
export const webDefaults = Object.freeze({ model: 'gpt-6.1-sol', effort: 'xhigh' as const,
  environment: 'mathlib' as const, maxTurns: 5, maxRunSeconds: 300, workers: 1, coordination: 'cooperative' as const });

export function getWebEnvironments(): WebEnvironmentOption[] {
  return (['standard', 'mathlib'] as WebEnvironment[]).map(id => {
    const trusted = getLeanTaskEnvironment(id);
    return { id, name: id === 'mathlib' ? 'Mathlib 数学库' : 'Lean 标准库',
      description: id === 'mathlib' ? '固定版本 Mathlib 数学库与预编译依赖。' : 'Lean 核心与标准库，无第三方数学依赖。',
      toolchain: trusted.toolchain, ...(trusted.mathlibRevision ? { mathlibRevision: trusted.mathlibRevision } : {}) };
  });
}
export const webTemplates: WebTemplate[] = [
  { id: 'addition', name: '自然数加法', environment: 'standard',
    source: 'namespace Tutorial\n\ntheorem add_zero (n : Nat) : n + 0 = n := by sorry\n\ntheorem zero_add (n : Nat) : 0 + n = n := by sorry\n\nend Tutorial\n',
    task: '证明两个自然数加法定理，保持原题声明不变。根据 Lean 反馈修复候选，并验收完整原题。' },
  { id: 'logic', name: '命题逻辑', environment: 'standard',
    source: 'namespace Logic\n\ntheorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by sorry\n\nend Logic\n',
    task: '构造这个命题逻辑定理的 Lean 证明，保留全部参数与命题。' },
  { id: 'polynomial', name: '实数多项式', environment: 'mathlib',
    source: 'import Mathlib\n\nnamespace Algebra\n\ntheorem square_add (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by sorry\n\nend Algebra\n',
    task: '使用 Mathlib 证明实数平方展开，可使用 ring 策略。保留原题的全部变量、类型与声明。' },
];
