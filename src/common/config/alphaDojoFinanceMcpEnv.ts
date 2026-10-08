import type { AlphaDojoFinanceConfig } from "./storage";

export const ALPHA_DOJO_SIDECAR_PROTOCOL = 'deepscientist.alpha_dojo.sidecar.v1' as const;
export const ALPHA_DOJO_SIDECAR_READY_SCHEMA = 'deepscientist.alpha_dojo.sidecar_ready.v1' as const;

export const ALPHA_DOJO_FINANCE_ENV_KEYS = {
  enabled: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_ENABLED',
  endpoint: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_ENDPOINT',
  defaultMarket: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_DEFAULT_MARKET',
  timezone: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_TIMEZONE',
  currency: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_CURRENCY',
  imagePrivacy: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_IMAGE_PRIVACY',
  allowSimulationWrites: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_ALLOW_SIMULATION_WRITES',
  allowScheduledMonitoring: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_ALLOW_SCHEDULED_MONITORING',
  timeoutMs: 'DEEPSCIENTIST_ALPHA_DOJO_FINANCE_TIMEOUT_MS',
} as const;

const defaultConfig: Required<Omit<AlphaDojoFinanceConfig, 'endpoint'>> & { endpoint?: string } = {
  enabled: true,
  defaultMarket: 'us',
  timezone: 'UTC',
  currency: 'USD',
  imagePrivacy: 'local_only',
  allowSimulationWrites: false,
  allowScheduledMonitoring: false,
  timeoutMs: 15_000,
};

export type ManagedAlphaDojoFinanceRuntime = {
  state: 'starting' | 'ready' | 'unavailable';
  managed: true;
  endpoint?: string;
  providerId: 'deepscientist-managed-alpha-dojo-finance';
  providerVersion: '1.0.0';
  reason?: string;
};

const boolFromEnv = (value: string | undefined, fallback: boolean): boolean =>
  value == null ? fallback : value === 'true';
const enumFromEnv = <T extends string>(value: string | undefined, allowed: readonly T[], fallback: T): T =>
  allowed.includes(value as T) ? (value as T) : fallback;

export const resolveAlphaDojoFinanceMcpEnv = (
  config?: AlphaDojoFinanceConfig,
  existingEnv: Record<string, string> = {}
): { config: AlphaDojoFinanceConfig; env: Record<string, string> } => {
  const resolved: AlphaDojoFinanceConfig = {
    enabled: config?.enabled ?? boolFromEnv(existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.enabled], defaultConfig.enabled),
    endpoint: config?.endpoint?.trim() || existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.endpoint]?.trim() || undefined,
    defaultMarket:
      config?.defaultMarket ||
      enumFromEnv(
        existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.defaultMarket],
        ['us', 'cn', 'hk', 'cross_market'],
        defaultConfig.defaultMarket
      ),
    timezone: config?.timezone?.trim() || existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.timezone] || defaultConfig.timezone,
    currency: config?.currency?.trim() || existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.currency] || defaultConfig.currency,
    imagePrivacy:
      config?.imagePrivacy ||
      enumFromEnv(
        existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.imagePrivacy],
        ['local_only', 'ask_each_time', 'allow_cloud'],
        defaultConfig.imagePrivacy
      ),
    allowSimulationWrites:
      config?.allowSimulationWrites ??
      boolFromEnv(existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.allowSimulationWrites], defaultConfig.allowSimulationWrites),
    allowScheduledMonitoring:
      config?.allowScheduledMonitoring ??
      boolFromEnv(
        existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.allowScheduledMonitoring],
        defaultConfig.allowScheduledMonitoring
      ),
    timeoutMs: Math.min(
      120_000,
      Math.max(
        1_000,
        config?.timeoutMs || Number(existingEnv[ALPHA_DOJO_FINANCE_ENV_KEYS.timeoutMs]) || defaultConfig.timeoutMs
      )
    ),
  };
  const env: Record<string, string> = {
    [ALPHA_DOJO_FINANCE_ENV_KEYS.enabled]: resolved.enabled ? 'true' : 'false',
    [ALPHA_DOJO_FINANCE_ENV_KEYS.defaultMarket]: resolved.defaultMarket || defaultConfig.defaultMarket,
    [ALPHA_DOJO_FINANCE_ENV_KEYS.timezone]: resolved.timezone || defaultConfig.timezone,
    [ALPHA_DOJO_FINANCE_ENV_KEYS.currency]: resolved.currency || defaultConfig.currency,
    [ALPHA_DOJO_FINANCE_ENV_KEYS.imagePrivacy]: resolved.imagePrivacy || defaultConfig.imagePrivacy,
    [ALPHA_DOJO_FINANCE_ENV_KEYS.allowSimulationWrites]: resolved.allowSimulationWrites ? 'true' : 'false',
    [ALPHA_DOJO_FINANCE_ENV_KEYS.allowScheduledMonitoring]: resolved.allowScheduledMonitoring ? 'true' : 'false',
    [ALPHA_DOJO_FINANCE_ENV_KEYS.timeoutMs]: String(resolved.timeoutMs),
  };
  if (resolved.endpoint) env[ALPHA_DOJO_FINANCE_ENV_KEYS.endpoint] = resolved.endpoint;
  return { config: resolved, env };
};

export const resolveAlphaDojoFinanceConfigWithManagedRuntime = (
  config?: AlphaDojoFinanceConfig,
  runtime?: Pick<ManagedAlphaDojoFinanceRuntime, 'state' | 'endpoint'>
): AlphaDojoFinanceConfig =>
  resolveAlphaDojoFinanceMcpEnv(
    config,
    runtime?.state === 'ready' && runtime.endpoint
      ? {
          [ALPHA_DOJO_FINANCE_ENV_KEYS.enabled]: 'true',
          [ALPHA_DOJO_FINANCE_ENV_KEYS.endpoint]: runtime.endpoint,
        }
      : {}
  ).config;
