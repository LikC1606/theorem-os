/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type { MedicalEvidenceConfig, ResearchEvidenceConfig } from "./storage";
import { MEDICAL_EVIDENCE_DEFAULT_PAPERCLIP_SOURCES } from "../chat/medicalEvidenceDefaults";
import { resolvePaperclipCredentialFields } from "./paperclipConfig";

export const RESEARCH_EVIDENCE_ENV_KEYS = {
  apiKey: 'PAPERCLIP_API_KEY',
  paperclipEnabled: 'PAPERCLIP_ENABLED',
  baseUrl: 'PAPERCLIP_BASE_URL',
  defaultSources: 'PAPERCLIP_DEFAULT_SOURCES',
  timeoutMs: 'PAPERCLIP_TIMEOUT_MS',
  enabledProviders: 'DEEPSCIENTIST_RESEARCH_EVIDENCE_PROVIDERS',
  literatureSearchEnabled: 'DEEPSCIENTIST_LITERATURE_SEARCH_ENABLED',
  literatureSearchDefaultSources: 'DEEPSCIENTIST_LITERATURE_SEARCH_SOURCES',
  semanticScholarApiKey: 'SEMANTIC_SCHOLAR_API_KEY',
  openAlexApiKey: 'OPENALEX_API_KEY',
  openAlexEmail: 'OPENALEX_EMAIL',
  crossrefEmail: 'CROSSREF_MAILTO',
  crossrefApiToken: 'CROSSREF_API_TOKEN',
  bioToolsEnabled: 'DEEPSCIENTIST_BIO_TOOLS_ENABLED',
  bioToolsPythonPath: 'DEEPSCIENTIST_BIO_TOOLS_PYTHON',
  bioToolsServerRoot: 'DEEPSCIENTIST_BIO_TOOLS_SERVER_ROOT',
  bioToolsDefaultDomains: 'DEEPSCIENTIST_BIO_TOOLS_DOMAINS',
} as const;

const DEFAULT_PAPERCLIP_BASE_URL = 'https://paperclip.gxl.ai';
const DEFAULT_PAPERCLIP_SOURCES = MEDICAL_EVIDENCE_DEFAULT_PAPERCLIP_SOURCES;
const DEFAULT_LITERATURE_SEARCH_SOURCES = [
  'semantic_scholar',
  'openalex',
  'arxiv',
  'openreview',
  'crossref',
  'dblp',
] as const;
const DEFAULT_BIO_TOOLS_DOMAINS = [
  'pubmed',
  'biorxiv',
  'chembl',
  'structures-interactions',
  'omics-archives',
  'genes-ontologies',
] as const;

export type ResearchEvidenceMcpEnvResolveResult =
  | {
      ok: true;
      env: Record<string, string>;
      config: ResearchEvidenceConfig;
    }
  | {
      ok: false;
      reason: 'no_provider';
      message: string;
      env: Record<string, string>;
      config?: ResearchEvidenceConfig;
    };

export function resolveBioToolsPythonPath(configuredPath?: string, bundledPath?: string): string | undefined {
  const configured = configuredPath?.trim();
  const bundled = bundledPath?.trim();
  if (configured && configured !== 'python3') return configured;
  return bundled || configured;
}

export function removeResearchEvidenceEnvKeys(env?: Record<string, string>): Record<string, string> {
  const next = { ...env };
  for (const key of Object.values(RESEARCH_EVIDENCE_ENV_KEYS)) {
    delete next[key];
  }
  return next;
}

export function resolveResearchEvidenceMcpEnv(
  config?: ResearchEvidenceConfig,
  existingEnv?: Record<string, string>,
  fallbackMedicalConfig?: MedicalEvidenceConfig
): ResearchEvidenceMcpEnvResolveResult {
  const shared = resolvePaperclipCredentialFields(
    config,
    fallbackMedicalConfig,
    existingEnv,
    RESEARCH_EVIDENCE_ENV_KEYS,
    {
      paperclipBaseUrl: DEFAULT_PAPERCLIP_BASE_URL,
      timeoutMs: 30000,
    }
  );
  const apiKey = shared.paperclipApiKey;
  const baseUrl = shared.paperclipBaseUrl;
  const defaultSources = config?.defaultSources?.length
    ? config.defaultSources
    : (existingEnv?.[RESEARCH_EVIDENCE_ENV_KEYS.defaultSources]?.split(',').filter(Boolean) ?? [
        ...DEFAULT_PAPERCLIP_SOURCES,
      ]);
  const timeoutMs = shared.timeoutMs;
  const paperclipReady = Boolean(apiKey);
  const literatureSearchEnabled =
    config?.literatureSearchEnabled ??
    (existingEnv?.[RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchEnabled]
      ? existingEnv[RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchEnabled] !== 'false'
      : true);
  const literatureSearchDefaultSources = config?.literatureSearchDefaultSources?.length
    ? config.literatureSearchDefaultSources
    : (existingEnv?.[RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchDefaultSources]?.split(',').filter(Boolean) ?? [
        ...DEFAULT_LITERATURE_SEARCH_SOURCES,
      ]);
  const bioToolsEnabled = config?.bioToolsEnabled === true;
  const bioToolsPythonPath = resolveBioToolsPythonPath(
    config?.bioToolsPythonPath,
    existingEnv?.[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsPythonPath]
  );
  const bioToolsServerRoot =
    config?.bioToolsServerRoot?.trim() || existingEnv?.[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsServerRoot]?.trim();
  const bioToolsDefaultDomains = config?.bioToolsDefaultDomains?.length
    ? config.bioToolsDefaultDomains
    : (existingEnv?.[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsDefaultDomains]?.split(',').filter(Boolean) ?? [
        ...DEFAULT_BIO_TOOLS_DOMAINS,
      ]);
  const enabledProviders = [
    paperclipReady ? 'paperclip' : undefined,
    literatureSearchEnabled ? 'paper_search' : undefined,
    bioToolsEnabled ? 'bio_tools' : undefined,
  ].filter(Boolean) as string[];

  const env: Record<string, string> = {
    [RESEARCH_EVIDENCE_ENV_KEYS.paperclipEnabled]: paperclipReady ? 'true' : 'false',
    [RESEARCH_EVIDENCE_ENV_KEYS.baseUrl]: baseUrl,
    [RESEARCH_EVIDENCE_ENV_KEYS.defaultSources]: defaultSources.join(','),
    [RESEARCH_EVIDENCE_ENV_KEYS.timeoutMs]: String(timeoutMs),
    [RESEARCH_EVIDENCE_ENV_KEYS.enabledProviders]: enabledProviders.join(','),
    [RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchEnabled]: literatureSearchEnabled ? 'true' : 'false',
    [RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchDefaultSources]: literatureSearchDefaultSources.join(','),
    [RESEARCH_EVIDENCE_ENV_KEYS.bioToolsEnabled]: bioToolsEnabled ? 'true' : 'false',
    [RESEARCH_EVIDENCE_ENV_KEYS.bioToolsDefaultDomains]: bioToolsDefaultDomains.join(','),
  };

  if (apiKey) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.apiKey] = apiKey;
  }
  if (bioToolsPythonPath) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsPythonPath] = bioToolsPythonPath;
  }
  if (bioToolsServerRoot) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsServerRoot] = bioToolsServerRoot;
  }
  if (config?.semanticScholarApiKey?.trim()) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.semanticScholarApiKey] = config.semanticScholarApiKey.trim();
  }
  if (config?.openAlexApiKey?.trim()) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.openAlexApiKey] = config.openAlexApiKey.trim();
  }
  if (config?.openAlexEmail?.trim()) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.openAlexEmail] = config.openAlexEmail.trim();
  }
  if (config?.crossrefEmail?.trim()) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.crossrefEmail] = config.crossrefEmail.trim();
  }
  if (config?.crossrefApiToken?.trim()) {
    env[RESEARCH_EVIDENCE_ENV_KEYS.crossrefApiToken] = config.crossrefApiToken.trim();
  }

  if (enabledProviders.length) {
    return {
      ok: true,
      env,
      config: {
        ...config,
        paperclipApiKey: apiKey,
        paperclipBaseUrl: baseUrl,
        defaultSources,
        timeoutMs,
        literatureSearchEnabled,
        literatureSearchDefaultSources,
        semanticScholarApiKey: config?.semanticScholarApiKey,
        openAlexApiKey: config?.openAlexApiKey,
        openAlexEmail: config?.openAlexEmail,
        crossrefEmail: config?.crossrefEmail,
        crossrefApiToken: config?.crossrefApiToken,
        bioToolsEnabled,
        bioToolsPythonPath,
        bioToolsServerRoot,
        bioToolsDefaultDomains,
      },
    };
  }

  return {
    ok: false,
    reason: 'no_provider',
    message: 'No research evidence provider is configured.',
    env,
    config,
  };
}
