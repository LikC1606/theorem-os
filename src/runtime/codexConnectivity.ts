import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { runMathProcess } from '../math/mathProcess';

/** Check the provider route without credentials, inference, or a model session. */
export async function checkCodexProviderConnectivity(input: {
  profile: string; env: NodeJS.ProcessEnv; signal?: AbortSignal;
}): Promise<{ status: 'reachable' | 'unavailable'; httpStatus?: number; diagnostics?: string }> {
  const configFile = path.join(input.profile, 'config.toml');
  const config = fs.existsSync(configFile) ? parseToml(fs.readFileSync(configFile, 'utf8')) : {};
  const provider = config.model_providers && typeof config.model_providers === 'object' &&
    typeof config.model_provider === 'string' ? config.model_providers[config.model_provider] : undefined;
  const base = provider && typeof provider === 'object' && typeof provider.base_url === 'string'
    ? provider.base_url : 'https://api.openai.com/v1';
  const endpoint = new URL(base);
  if (!['http:', 'https:'].includes(endpoint.protocol) || endpoint.username || endpoint.password || endpoint.search)
    return { status: 'unavailable', diagnostics: 'Provider connectivity check requires an HTTP(S) base URL without credentials or query parameters.' };
  endpoint.pathname = endpoint.pathname.replace(/\/$/u, '') + '/models';
  endpoint.hash = '';
  const result = await runMathProcess('/usr/bin/curl', ['--head', '--silent', '--output', '/dev/null',
    '--connect-timeout', '3', '--max-time', '8', '--write-out', '%{http_code}', endpoint.href],
  { cwd: process.cwd(), env: input.env, signal: input.signal, timeoutMs: 10_000 });
  const httpStatus = Number(result.stdout.trim());
  if (result.exitCode === 0 && httpStatus >= 100 && httpStatus <= 599 && httpStatus !== 407)
    return { status: 'reachable', httpStatus };
  return { status: 'unavailable', ...(httpStatus > 0 ? { httpStatus } : {}),
    diagnostics: httpStatus === 407 ? 'Provider proxy requires authentication.' :
      `Provider connection failed (curl exit ${result.exitCode ?? 'unavailable'}). Check the proxy on this host and the route to the configured provider.` };
}
