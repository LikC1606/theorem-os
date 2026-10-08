/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { z } from 'zod';
import { RESEARCH_EVIDENCE_ENV_KEYS } from "../common/config/researchEvidenceMcpEnv";
import { assertResearchTeamToolActionAuthorized } from "../common/types/team/researchTeamToolPolicy";
import { BUILTIN_RESEARCH_EVIDENCE_NAME } from "./constants";
import {
  DEFAULT_LITERATURE_SEARCH_SOURCES,
  LITERATURE_SEARCH_PROVIDER,
  isLiteratureSearchSource,
  normalizeLiteratureSearchSources,
  searchLiterature,
} from "./literatureSearch";
import { ORIGENE_SERVICES, OrigeneGateway } from "./origeneGateway";
import { buildCompactLiteratureSearchPayload } from "./researchEvidencePayload";
import {
  TARGET_DISCOVERY_BATCH_CONCURRENCY,
  TARGET_DISCOVERY_BATCH_LIMIT,
  assessTargetDiscoveryToolResult,
  mapSettledWithConcurrency,
  type TargetDiscoveryToolResult,
} from "./researchEvidenceTargetDiscovery";

const DEFAULT_BASE_URL = 'https://paperclip.gxl.ai';
const DEFAULT_TIMEOUT_MS = 30000;
const RESULT_SCHEMA = 'deepscientist.research_evidence.result.v2';

type ProviderName = 'paperclip' | 'bio_tools' | 'origene' | typeof LITERATURE_SEARCH_PROVIDER;

type PaperclipMcpResponse = {
  result?: {
    content?: Array<{ type?: string; text?: string }>;
  };
  error?: {
    message?: string;
  };
};

type BioTool = {
  name: string;
  description?: string;
  inputSchema?: Record<string, unknown>;
};

type BioToolCallResult = {
  content?: Array<{ type?: string; text?: string; data?: string; mimeType?: string }>;
  structuredContent?: unknown;
  isError?: boolean;
  [key: string]: unknown;
};

type TargetDiscoveryCall = {
  id?: string;
  service: string;
  tool: string;
  arguments?: Record<string, unknown>;
};

type EvidenceDraft = {
  title: string;
  sourceType: 'paper' | 'database_record' | 'dataset';
  claimType: 'parsed';
  confidence: 'moderate';
  status: 'available' | 'needs_review';
  summary?: string;
  url?: string;
  database: {
    name: string;
    provider: ProviderName;
    domain?: string;
    tool?: string;
    endpoint?: string;
    params?: Record<string, unknown>;
    accessDate: string;
    returnedCount?: number;
    retrievedCount?: number;
    warnings?: string[];
  };
};

type BioSearchRoute = {
  tool: string;
  databaseName: string;
  domain: string;
  sourceType: EvidenceDraft['sourceType'];
  buildArguments: (query: string, maxResults: number) => Record<string, unknown>;
};

const jsonText = (value: unknown, isError = false) => ({
  content: [{ type: 'text' as const, text: JSON.stringify(value, null, 2) }],
  ...(isError ? { isError: true as const } : {}),
});

const previewOutput = (output: string, maxLength = 1600): string => {
  const trimmed = output.trim();
  if (trimmed.length <= maxLength) return trimmed;
  return `${trimmed.slice(0, maxLength).trimEnd()}\n...`;
};

const parseFoundCount = (output: string): number => {
  const match = output.match(/Found\s+(\d+)\s+(?:results|papers|records|items)/iu);
  if (match) return Number(match[1]) || 0;
  const numbered = output.match(/^\s*\d+\.\s+/gmu);
  return numbered?.length || 0;
};

const parseSavedSearchId = (output: string): string | undefined => {
  const match = output.match(/saved\s+as\s+(s_[A-Za-z0-9_-]+)/i) || output.match(/\b(s_[A-Za-z0-9_-]+)\b/u);
  return match?.[1];
};

const safeJsonParse = (value: string): unknown => {
  try {
    return JSON.parse(value);
  } catch {
    return undefined;
  }
};

const normalizeSource = (source: string): string => (source === 'clinicaltrials' ? 'trials/us' : source);

const normalizeBioSource = (source?: string): string =>
  (source || '').trim().toLowerCase().replace(/\s+/gu, '_').replace(/-/gu, '_');

const firstString = (value: unknown): string | undefined => {
  if (typeof value === 'string' && value.trim()) return value.trim();
  return undefined;
};

const countFromStructured = (value: unknown): { returnedCount?: number; retrievedCount?: number } => {
  if (!value || typeof value !== 'object') return {};
  const record = value as Record<string, unknown>;
  const returned =
    Number(record.total_count) ||
    Number(record.total) ||
    Number(record.count) ||
    Number(record.totalCount) ||
    Number(record.returnedCount) ||
    undefined;
  const collections = ['records', 'results', 'articles', 'molecules', 'targets', 'studies', 'models'];
  for (const key of collections) {
    const item = record[key];
    if (Array.isArray(item)) {
      return { returnedCount: returned, retrievedCount: item.length };
    }
  }
  return { returnedCount: returned };
};

const titleFromStructured = (
  tool: string,
  source: string | undefined,
  query: string | undefined,
  value: unknown
): string => {
  if (value && typeof value === 'object') {
    const record = value as Record<string, unknown>;
    const records = record.records || record.results || record.articles || record.molecules || record.targets;
    if (Array.isArray(records) && records.length) {
      const first = records[0] as Record<string, unknown>;
      return (
        firstString(first.title) ||
        firstString(first.name) ||
        firstString(first.pref_name) ||
        firstString(first.accession) ||
        firstString(first.id) ||
        `${tool}: ${query || source || 'result'}`
      );
    }
  }
  return `${tool}: ${query || source || 'result'}`;
};

const stripSchemas = (tool: BioTool, domain?: string) => ({
  name: tool.name,
  description: tool.description,
  domain,
});

const inheritedEnv = (): Record<string, string> => {
  // bio-tools is an external Python MCP process. Keep the runtime, proxy and
  // explicitly documented provider credentials, but never persist unrelated
  // desktop/cloud secrets in its stdio transport configuration.
  const allowedKeys = [
    'PATH',
    'HOME',
    'USERPROFILE',
    'TMPDIR',
    'TMP',
    'TEMP',
    'LANG',
    'LC_ALL',
    'LC_CTYPE',
    'HTTP_PROXY',
    'HTTPS_PROXY',
    'NO_PROXY',
    'http_proxy',
    'https_proxy',
    'no_proxy',
    'ALL_PROXY',
    'all_proxy',
    'SSL_CERT_FILE',
    'SSL_CERT_DIR',
    'REQUESTS_CA_BUNDLE',
    'NCBI_API_KEY',
    'NCBI_EMAIL',
    'PUBMED_EMAIL',
    'VIRTUAL_ENV',
  ];
  const env: Record<string, string> = {};
  for (const key of allowedKeys) {
    const value = process.env[key];
    if (typeof value === 'string') env[key] = value;
  }
  for (const [key, value] of Object.entries(process.env)) {
    if (typeof value === 'string' && /^DEEPSCIENTIST_BIO_TOOLS_/iu.test(key)) env[key] = value;
  }
  return env;
};

const bioToolSearchRoutes: Record<string, BioSearchRoute> = {
  pubmed: {
    tool: 'search_articles',
    databaseName: 'PubMed',
    domain: 'pubmed',
    sourceType: 'paper',
    buildArguments: (query, maxResults) => ({ query, max_results: maxResults }),
  },
  ncbi_pubmed: {
    tool: 'search_articles',
    databaseName: 'PubMed',
    domain: 'pubmed',
    sourceType: 'paper',
    buildArguments: (query, maxResults) => ({ query, max_results: maxResults }),
  },
  chembl: {
    tool: 'compound_search',
    databaseName: 'ChEMBL',
    domain: 'chembl',
    sourceType: 'database_record',
    buildArguments: (query, maxResults) => ({ name: query, limit: maxResults }),
  },
  chembl_compound: {
    tool: 'compound_search',
    databaseName: 'ChEMBL',
    domain: 'chembl',
    sourceType: 'database_record',
    buildArguments: (query, maxResults) => ({ name: query, limit: maxResults }),
  },
  chembl_target: {
    tool: 'target_search',
    databaseName: 'ChEMBL Target',
    domain: 'chembl',
    sourceType: 'database_record',
    buildArguments: (query, maxResults) => ({ gene_symbol: query, limit: maxResults }),
  },
  geo: {
    tool: 'geo_search_series',
    databaseName: 'NCBI GEO',
    domain: 'omics-archives',
    sourceType: 'dataset',
    buildArguments: (query, maxResults) => ({ term: query, retmax: maxResults }),
  },
  ncbi_geo: {
    tool: 'geo_search_series',
    databaseName: 'NCBI GEO',
    domain: 'omics-archives',
    sourceType: 'dataset',
    buildArguments: (query, maxResults) => ({ term: query, retmax: maxResults }),
  },
  alphafold: {
    tool: 'alphafold_get_prediction',
    databaseName: 'AlphaFold DB',
    domain: 'structures-interactions',
    sourceType: 'database_record',
    buildArguments: (query) => ({ uniprot_accession: query }),
  },
  alphafold_db: {
    tool: 'alphafold_get_prediction',
    databaseName: 'AlphaFold DB',
    domain: 'structures-interactions',
    sourceType: 'database_record',
    buildArguments: (query) => ({ uniprot_accession: query }),
  },
};

class PaperclipGateway {
  private readonly apiKey = process.env[RESEARCH_EVIDENCE_ENV_KEYS.apiKey] || '';
  private readonly baseUrl = (process.env[RESEARCH_EVIDENCE_ENV_KEYS.baseUrl] || DEFAULT_BASE_URL).replace(/\/+$/u, '');
  private readonly timeoutMs = Number(process.env[RESEARCH_EVIDENCE_ENV_KEYS.timeoutMs] || DEFAULT_TIMEOUT_MS);
  readonly enabled =
    process.env[RESEARCH_EVIDENCE_ENV_KEYS.paperclipEnabled] !== 'false' && Boolean(this.apiKey.trim());

  status() {
    return {
      provider: 'paperclip' as const,
      enabled: this.enabled,
      configured: Boolean(this.apiKey.trim()),
      baseUrl: this.baseUrl,
    };
  }

  async call(command: string): Promise<string> {
    if (!this.enabled) {
      throw new Error('PaperClip is not configured. Add a PaperClip API key in Science settings to enable it.');
    }

    const controller = new AbortController();
    const timer = setTimeout(
      () => controller.abort(),
      Number.isFinite(this.timeoutMs) ? this.timeoutMs : DEFAULT_TIMEOUT_MS
    );
    try {
      const response = await fetch(`${this.baseUrl}/mcp`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'X-API-Key': this.apiKey,
        },
        body: JSON.stringify({
          jsonrpc: '2.0',
          id: `deepscientist-research-evidence-${Date.now()}`,
          method: 'tools/call',
          params: {
            name: 'paperclip',
            arguments: { command },
          },
        }),
        signal: controller.signal,
      });
      if (!response.ok) {
        throw new Error(`PaperClip request failed (${response.status})`);
      }
      const payload = (await response.json()) as PaperclipMcpResponse;
      if (payload.error?.message) {
        throw new Error(payload.error.message);
      }
      return (payload.result?.content || [])
        .map((item) => (item.type === 'text' ? item.text || '' : ''))
        .filter(Boolean)
        .join('\n');
    } finally {
      clearTimeout(timer);
    }
  }
}

class BioToolsGateway {
  private client?: Client;
  private transport?: StdioClientTransport;
  private domains?: Record<string, string[]>;
  readonly enabled = process.env[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsEnabled] === 'true';
  readonly pythonPath =
    process.env[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsPythonPath] || (process.platform === 'win32' ? 'python' : 'python3');
  readonly defaultDomains = (process.env[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsDefaultDomains] || '')
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);
  readonly serverRoot = this.resolveServerRoot();

  status() {
    const configured = Boolean(this.serverRoot && existsSync(path.join(this.serverRoot, 'run_server.py')));
    return {
      provider: 'bio_tools' as const,
      enabled: this.enabled,
      configured,
      pythonPath: this.pythonPath,
      serverRoot: this.serverRoot,
      defaultDomains: this.defaultDomains,
      connected: Boolean(this.client),
    };
  }

  async listTools(domain?: string, includeSchemas = false): Promise<Array<Record<string, unknown>>> {
    const client = await this.ensureClient();
    const tools = (await client.listTools()).tools as BioTool[];
    const domains = this.readDomains();
    const toolToDomain = new Map<string, string>();
    for (const [domainName, toolNames] of Object.entries(domains)) {
      for (const toolName of toolNames) toolToDomain.set(toolName, domainName);
    }
    return tools
      .filter((tool) => !domain || toolToDomain.get(tool.name) === domain)
      .map((tool) =>
        includeSchemas
          ? { ...tool, domain: toolToDomain.get(tool.name) }
          : stripSchemas(tool, toolToDomain.get(tool.name))
      );
  }

  async callTool(tool: string, args: Record<string, unknown>): Promise<BioToolCallResult> {
    const client = await this.ensureClient();
    return (await client.callTool({ name: tool, arguments: args })) as BioToolCallResult;
  }

  toolDomain(tool: string): string | undefined {
    const domains = this.readDomains();
    for (const [domainName, tools] of Object.entries(domains)) {
      if (tools.includes(tool)) return domainName;
    }
    return undefined;
  }

  private resolveServerRoot(): string | undefined {
    const resourcesPath = (process as typeof process & { resourcesPath?: string }).resourcesPath;
    const currentDir = path.dirname(fileURLToPath(import.meta.url));
    const candidates = [
      process.env[RESEARCH_EVIDENCE_ENV_KEYS.bioToolsServerRoot],
      path.resolve(process.cwd(), 'resources/skills/vendor/science-skills/mcp-servers/bio-tools'),
      path.resolve(process.cwd(), 'resources/skills/vendor/JimLiu-science-skills/mcp-servers/bio-tools'),
      resourcesPath ? path.resolve(resourcesPath, 'skills/vendor/science-skills/mcp-servers/bio-tools') : undefined,
      path.resolve(currentDir, '../../resources/skills/vendor/science-skills/mcp-servers/bio-tools'),
      '/tmp/jimli-science-skills/mcp-servers/bio-tools',
    ].filter(Boolean) as string[];
    return candidates.find((candidate) => existsSync(path.join(candidate, 'run_server.py')));
  }

  private readDomains(): Record<string, string[]> {
    if (this.domains) return this.domains;
    const domainPath = this.serverRoot ? path.join(this.serverRoot, 'lib/mcp_bio/domains.json') : '';
    if (!domainPath || !existsSync(domainPath)) {
      this.domains = {};
      return this.domains;
    }
    try {
      this.domains = JSON.parse(readFileSync(domainPath, 'utf8')) as Record<string, string[]>;
    } catch {
      this.domains = {};
    }
    return this.domains;
  }

  private async ensureClient(): Promise<Client> {
    if (!this.enabled) {
      throw new Error(
        'bio-tools provider is disabled. Enable it in Science settings before using provider="bio_tools".'
      );
    }
    if (!this.serverRoot) {
      throw new Error('bio-tools server root was not found. Set the bio-tools server root in Science settings.');
    }
    if (this.client) return this.client;

    const libPath = path.join(this.serverRoot, 'lib');
    const env = inheritedEnv();
    env.PYTHONUNBUFFERED = '1';
    env.PYTHONPATH = env.PYTHONPATH ? `${libPath}${path.delimiter}${env.PYTHONPATH}` : libPath;
    const transport = new StdioClientTransport({
      command: this.pythonPath,
      args: [path.join(this.serverRoot, 'run_server.py'), 'mcp_bio'],
      cwd: this.serverRoot,
      env,
      stderr: 'pipe',
    });
    const client = new Client({ name: 'deepscientist-research-evidence-bio-tools', version: '1.0.0' });
    const stderrChunks: string[] = [];
    transport.stderr?.on('data', (chunk) => {
      stderrChunks.push(String(chunk));
      if (stderrChunks.join('').length > 8000) stderrChunks.splice(0, stderrChunks.length - 4);
    });
    try {
      await client.connect(transport);
    } catch (error) {
      const stderr = previewOutput(stderrChunks.join('\n'), 1200);
      await transport.close().catch((): undefined => undefined);
      throw new Error(
        [
          'bio-tools MCP could not start.',
          `Python: ${this.pythonPath}`,
          `Server root: ${this.serverRoot}`,
          stderr ? `stderr: ${stderr}` : error instanceof Error ? `error: ${error.message}` : undefined,
          'Configure a Python environment with the JimLiu science-skills bio-tools dependencies installed.',
        ]
          .filter(Boolean)
          .join('\n')
      );
    }
    this.transport = transport;
    this.client = client;
    return client;
  }
}

class LiteratureSearchGateway {
  readonly enabled = process.env[RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchEnabled] !== 'false';
  readonly defaultSources = normalizeLiteratureSearchSources(
    (
      process.env[RESEARCH_EVIDENCE_ENV_KEYS.literatureSearchDefaultSources] ||
      DEFAULT_LITERATURE_SEARCH_SOURCES.join(',')
    )
      .split(',')
      .filter(Boolean)
  );
  private readonly semanticScholarApiKey = process.env[RESEARCH_EVIDENCE_ENV_KEYS.semanticScholarApiKey] || '';
  private readonly openAlexApiKey = process.env[RESEARCH_EVIDENCE_ENV_KEYS.openAlexApiKey] || '';
  private readonly openAlexEmail = process.env[RESEARCH_EVIDENCE_ENV_KEYS.openAlexEmail] || '';
  private readonly crossrefEmail = process.env[RESEARCH_EVIDENCE_ENV_KEYS.crossrefEmail] || '';
  private readonly crossrefApiToken = process.env[RESEARCH_EVIDENCE_ENV_KEYS.crossrefApiToken] || '';
  private readonly timeoutMs = Number(process.env[RESEARCH_EVIDENCE_ENV_KEYS.timeoutMs] || DEFAULT_TIMEOUT_MS);

  status() {
    return {
      provider: LITERATURE_SEARCH_PROVIDER,
      enabled: this.enabled,
      configured: this.enabled,
      defaultSources: this.defaultSources,
      apiKeys: {
        semanticScholar: Boolean(this.semanticScholarApiKey.trim()),
        openAlex: Boolean(this.openAlexApiKey.trim()),
        crossrefPlus: Boolean(this.crossrefApiToken.trim()),
      },
      contact: {
        openAlexEmail: Boolean(this.openAlexEmail.trim()),
        crossrefEmail: Boolean(this.crossrefEmail.trim()),
      },
    };
  }

  async search({
    query,
    sources,
    maxResults,
    startYear,
    endYear,
  }: {
    query: string;
    sources?: string[];
    maxResults: number;
    startYear?: number;
    endYear?: number;
  }) {
    if (!this.enabled) {
      throw new Error('Paper search provider is disabled. Enable enhanced literature search in Science settings.');
    }
    return searchLiterature({
      query,
      maxResults,
      sources: sources?.length ? sources : this.defaultSources,
      startYear,
      endYear,
      timeoutMs: Number.isFinite(this.timeoutMs) ? this.timeoutMs : DEFAULT_TIMEOUT_MS,
      semanticScholarApiKey: this.semanticScholarApiKey,
      openAlexApiKey: this.openAlexApiKey,
      openAlexEmail: this.openAlexEmail,
      crossrefEmail: this.crossrefEmail,
      crossrefApiToken: this.crossrefApiToken,
    });
  }
}

const resultText = (result: BioToolCallResult): string => {
  const text = (result.content || [])
    .map((item) => (item.type === 'text' ? item.text || '' : ''))
    .filter(Boolean)
    .join('\n');
  if (text.trim()) return text;
  if (result.structuredContent != null) return JSON.stringify(result.structuredContent);
  return JSON.stringify(result);
};

const targetDiscoveryServiceGuidance = [
  {
    services: ['opentargets_mcp', 'clinicaltrials_mcp', 'fda_drug_mcp', 'monarch_mcp'],
    purpose: 'Known target, trial, regulatory, phenotype, and safety context.',
  },
  {
    services: ['tcga_mcp', 'depmap_mcp'],
    purpose: 'Bounded source summaries and availability checks; not a substitute for local patient-cohort computation.',
  },
  {
    services: ['chembl_mcp', 'pubchem_mcp'],
    purpose: 'Bioactivity, tractability, compound identity, and chemistry context.',
  },
  {
    services: ['ncbi_mcp', 'ensembl_mcp', 'uniprot_mcp', 'ucsc_mcp', 'dbsearch_mcp'],
    purpose: 'Gene, protein, variant, transcript, and genome identity resolution.',
  },
  {
    services: ['kegg_mcp', 'string_mcp', 'pdb_mcp'],
    purpose: 'Pathway, interaction-network, and experimental-structure context.',
  },
  {
    services: ['search_mcp'],
    purpose: 'Cross-source discovery only; snippets remain retrieval context and require source verification.',
  },
] as const;

const targetDiscoveryDescription = () => ({
  schema: RESULT_SCHEMA,
  action: 'describe',
  provider: 'origene',
  capability: 'bounded scientific database retrieval',
  evidenceClass: 'parsed',
  claimCeiling:
    'Database association or retrieved source context. This tool does not establish patient-level computation, causal validation, experimental validation, or target novelty.',
  actions: {
    describe: 'Return this complete usage and evidence-boundary contract without starting the Origene runtime.',
    status:
      'Inspect runtime readiness and the complete service list. One status call is sufficient until state changes.',
    prepare: 'Start lazy preparation of the pinned local runtime, then use status until prepareState is ready.',
    list_tools: 'Inspect exact tools for one service. Set includeSchemas=true when arguments are not already known.',
    call: 'Run one exact service tool and return raw output plus one parsed-evidence draft.',
    batch_call: `Run 1-${TARGET_DISCOVERY_BATCH_LIMIT} independent calls with at most ${TARGET_DISCOVERY_BATCH_CONCURRENCY} active calls. Results preserve input order and isolate failures.`,
  },
  batchContract: {
    maxCalls: TARGET_DISCOVERY_BATCH_LIMIT,
    maxConcurrency: TARGET_DISCOVERY_BATCH_CONCURRENCY,
    stableInputOrder: true,
    partialFailureIsolation: true,
    item: {
      id: 'Optional caller correlation id; defaults to call-<1-based index>.',
      service: 'Exact Origene service name.',
      tool: 'Exact tool name returned by list_tools.',
      arguments: 'Tool arguments matching its input schema.',
    },
  },
  evidencePolicy: {
    success:
      'Evidence drafts use status=available only when the MCP envelope and returned JSON contain no failure signal.',
    failure:
      'MCP isError, error, success=false, ok=false, and status=error|failed produce ok=false and status=needs_review.',
    computation:
      'Use biomedical_execution or a project-native, receipt-producing workflow for matrices, patient-level QC, modelling, and cross-cohort computation.',
  },
  workflow: [
    'Call describe once when routing is unclear.',
    'Call status once; prepare only when the runtime is not ready.',
    'Call list_tools once per needed service and reuse the returned schema.',
    'Use batch_call for independent candidate or cross-database checks instead of repeating equivalent control calls.',
    'Register material outputs as Science evidence and preserve release, filters, access date, and warnings.',
  ],
  services: ORIGENE_SERVICES,
  serviceGuidance: targetDiscoveryServiceGuidance,
  timestamp: Date.now(),
});

const buildOrigeneCallPayload = ({
  action,
  call,
  result,
}: {
  action: 'call' | 'batch_call';
  call: TargetDiscoveryCall;
  result: TargetDiscoveryToolResult;
}) => {
  const args = call.arguments || {};
  const output = resultText(result);
  const assessment = assessTargetDiscoveryToolResult(result);
  return {
    schema: RESULT_SCHEMA,
    action,
    provider: 'origene' as const,
    service: call.service,
    tool: call.tool,
    arguments: args,
    ok: assessment.ok,
    failure: assessment.failure,
    rawPreview: previewOutput(output),
    rawOutput: output,
    structuredContent: result.structuredContent,
    evidenceDrafts: [
      {
        title: `Origene ${call.service}.${call.tool}`,
        sourceType: 'database_record' as const,
        claimType: 'parsed' as const,
        confidence: 'moderate' as const,
        status: assessment.evidenceStatus,
        summary: previewOutput(output),
        database: {
          name: call.service,
          provider: 'origene' as const,
          domain: 'target-discovery',
          tool: call.tool,
          params: args,
          accessDate: new Date().toISOString(),
          warnings: assessment.warnings,
        },
      },
    ],
  };
};

const buildOrigeneThrownFailure = (call: TargetDiscoveryCall, error: unknown) => {
  const message = error instanceof Error ? error.message : String(error);
  return {
    schema: RESULT_SCHEMA,
    action: 'batch_call' as const,
    provider: 'origene' as const,
    service: call.service,
    tool: call.tool,
    arguments: call.arguments || {},
    ok: false,
    failure: { kind: 'exception' as const, reasons: [message] },
    evidenceDrafts: [
      {
        title: `Origene ${call.service}.${call.tool}`,
        sourceType: 'database_record' as const,
        claimType: 'parsed' as const,
        confidence: 'moderate' as const,
        status: 'needs_review' as const,
        summary: message,
        database: {
          name: call.service,
          provider: 'origene' as const,
          domain: 'target-discovery',
          tool: call.tool,
          params: call.arguments || {},
          accessDate: new Date().toISOString(),
          warnings: [`Origene tool call failed before returning a usable result: ${message}`],
        },
      },
    ],
  };
};

const buildBioEvidenceDraft = ({
  route,
  tool,
  args,
  query,
  output,
  structured,
}: {
  route?: BioSearchRoute;
  tool: string;
  args: Record<string, unknown>;
  query?: string;
  output: string;
  structured?: unknown;
}): EvidenceDraft => {
  const parsed = structured ?? safeJsonParse(output);
  const counts = countFromStructured(parsed);
  const domain = route?.domain;
  return {
    title: titleFromStructured(tool, domain, query, parsed),
    sourceType: route?.sourceType || 'database_record',
    claimType: 'parsed',
    confidence: 'moderate',
    status: 'available',
    summary: previewOutput(output, 360),
    database: {
      name: route?.databaseName || 'bio-tools',
      provider: 'bio_tools',
      domain,
      tool,
      params: args,
      accessDate: new Date().toISOString(),
      ...counts,
    },
  };
};

async function main() {
  const paperclip = new PaperclipGateway();
  const bioTools = new BioToolsGateway();
  const literatureSearch = new LiteratureSearchGateway();
  const origene = new OrigeneGateway();
  const server = new McpServer({
    name: BUILTIN_RESEARCH_EVIDENCE_NAME,
    version: '1.2.0',
  });

  const closeOrigene = () => {
    void origene.close();
  };
  const shutdown = (exitCode: number) => {
    void origene.close().finally(() => process.exit(exitCode));
  };
  process.once('SIGINT', () => shutdown(130));
  process.once('SIGTERM', () => shutdown(143));
  process.once('exit', closeOrigene);

  server.tool(
    'target_discovery',
    'Controlled bridge to vendored OrigeneMCP scientific database services. Use describe once for routing and evidence boundaries, then call or batch_call for bounded retrieval. Database associations remain parsed context, not patient-level computation or experimental validation.',
    {
      action: z.enum(['describe', 'status', 'prepare', 'list_services', 'list_tools', 'call', 'batch_call']),
      service: z
        .string()
        .optional()
        .describe('Origene service, for example opentargets_mcp, chembl_mcp, ncbi_mcp, or tcga_mcp.'),
      tool: z.string().optional().describe('Exact tool name returned by action="list_tools".'),
      arguments: z.record(z.unknown()).optional(),
      calls: z
        .array(
          z.object({
            id: z.string().min(1).max(128).optional(),
            service: z.string().min(1),
            tool: z.string().min(1),
            arguments: z.record(z.unknown()).optional(),
          })
        )
        .min(1)
        .max(TARGET_DISCOVERY_BATCH_LIMIT)
        .optional()
        .describe(
          `Independent calls for action="batch_call". At most ${TARGET_DISCOVERY_BATCH_LIMIT} calls run with concurrency ${TARGET_DISCOVERY_BATCH_CONCURRENCY}; results preserve input order.`
        ),
      includeSchemas: z.boolean().default(false),
    },
    async ({ action, service, tool, arguments: toolArguments, calls, includeSchemas }) => {
      if (action === 'describe') return jsonText(targetDiscoveryDescription());
      if (action === 'status') {
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'origene',
          status: origene.status(),
          timestamp: Date.now(),
        });
      }
      if (action === 'prepare') {
        const status = origene.beginPrepare();
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'origene',
          status,
          timestamp: Date.now(),
        });
      }
      if (action === 'list_services') {
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'origene',
          services: ORIGENE_SERVICES,
          timestamp: Date.now(),
        });
      }
      if (action === 'batch_call') {
        if (!calls?.length) throw new Error('target_discovery action="batch_call" requires calls.');
        const settled = await mapSettledWithConcurrency(calls, TARGET_DISCOVERY_BATCH_CONCURRENCY, async (call) => {
          if (!call.service || !call.tool) {
            throw new Error('Each target_discovery batch call requires service and tool.');
          }
          const normalizedCall: TargetDiscoveryCall = {
            id: call.id,
            service: call.service,
            tool: call.tool,
            arguments: call.arguments,
          };
          return buildOrigeneCallPayload({
            action,
            call: normalizedCall,
            result: await origene.callTool(normalizedCall.service, normalizedCall.tool, normalizedCall.arguments || {}),
          });
        });
        const results = settled.map((item, index) => {
          const call = calls[index] as TargetDiscoveryCall;
          const payload = item.status === 'fulfilled' ? item.value : buildOrigeneThrownFailure(call, item.reason);
          return {
            id: call.id || `call-${index + 1}`,
            index,
            ...payload,
          };
        });
        const succeeded = results.filter((item) => item.ok).length;
        const failed = results.length - succeeded;
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'origene',
          limits: {
            maxCalls: TARGET_DISCOVERY_BATCH_LIMIT,
            maxConcurrency: TARGET_DISCOVERY_BATCH_CONCURRENCY,
          },
          count: results.length,
          succeeded,
          failed,
          ok: failed === 0,
          status: failed === 0 ? 'complete' : succeeded === 0 ? 'failed' : 'partial_failure',
          results,
          timestamp: Date.now(),
        });
      }
      if (!service) throw new Error(`target_discovery action="${action}" requires service.`);
      if (action === 'list_tools') {
        const tools = await origene.listTools(service, includeSchemas);
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'origene',
          service,
          count: tools.length,
          tools,
          timestamp: Date.now(),
        });
      }
      if (!tool) throw new Error('target_discovery action="call" requires tool.');
      const payload = buildOrigeneCallPayload({
        action,
        call: { service, tool, arguments: toolArguments },
        result: await origene.callTool(service, tool, toolArguments || {}),
      });
      return jsonText(
        {
          ...payload,
          timestamp: Date.now(),
        },
        !payload.ok
      );
    }
  );

  server.tool(
    'research_evidence',
    'Unified research evidence control-plane tool for PaperClip literature/files and bio-tools scientific databases. For PaperClip full text, search first and then read a returned virtualPath or run an explicit cat command; PaperClip does not read arbitrary URLs. Search/read/call results should be registered as Science evidence via science_artifact when used in claims.',
    {
      action: z.enum(['status', 'list_tools', 'search', 'read', 'call']),
      provider: z.enum(['auto', 'paperclip', 'bio_tools', LITERATURE_SEARCH_PROVIDER]).default('auto'),
      mode: z.enum(['medical', 'science', 'general']).default('science'),
      query: z.string().optional(),
      source: z
        .string()
        .optional()
        .describe('PaperClip source or bio-tools source alias, e.g. pmc, pubmed, chembl, geo, alphafold.'),
      sources: z.array(z.string()).optional(),
      maxResults: z.number().min(1).max(50).default(8),
      startYear: z.number().int().min(1800).max(2200).optional(),
      endYear: z.number().int().min(1800).max(2200).optional(),
      sourceId: z.string().optional(),
      virtualPath: z
        .string()
        .optional()
        .describe('PaperClip virtual file path returned by a PaperClip search, such as /papers/<id>/content.lines.'),
      command: z
        .string()
        .optional()
        .describe(
          'Explicit PaperClip command for action="read" or provider="paperclip" call, without a binary prefix.'
        ),
      tool: z
        .string()
        .optional()
        .describe('bio-tools MCP tool name for action="call", e.g. search_articles, compound_search.'),
      arguments: z.record(z.unknown()).optional(),
      domain: z.string().optional().describe('Optional bio-tools domain filter for action="list_tools".'),
      includeSchemas: z.boolean().default(false),
      anchor: z
        .object({
          lineStart: z.number().optional(),
          lineEnd: z.number().optional(),
          page: z.number().optional(),
        })
        .optional(),
    },
    async ({
      action,
      provider,
      mode,
      query,
      source,
      sources,
      maxResults,
      startYear,
      endYear,
      sourceId,
      virtualPath,
      command,
      tool,
      arguments: toolArguments,
      domain,
      includeSchemas,
      anchor,
    }) => {
      // The ACP permission router controls interactive approval, while this
      // server-side check enforces the same role policy after a call has been
      // accepted. This prevents a Worker from using status/list_tools/call or
      // an explicit read command outside its injected capability.
      assertResearchTeamToolActionAuthorized('research_evidence', action);
      if (action === 'status') {
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          mode,
          providers: {
            paperclip: paperclip.status(),
            paper_search: literatureSearch.status(),
            bio_tools: bioTools.status(),
            origene: origene.status(),
          },
          timestamp: Date.now(),
        });
      }

      if (action === 'list_tools') {
        const resolvedProvider: ProviderName =
          provider === 'paperclip'
            ? 'paperclip'
            : provider === LITERATURE_SEARCH_PROVIDER
              ? LITERATURE_SEARCH_PROVIDER
              : 'bio_tools';
        if (resolvedProvider === 'paperclip') {
          return jsonText({
            schema: RESULT_SCHEMA,
            action,
            provider: 'paperclip',
            tools: [
              {
                name: 'paperclip',
                description: 'PaperClip command bridge: search, cat, and source-specific commands.',
              },
            ],
            timestamp: Date.now(),
          });
        }
        if (resolvedProvider === LITERATURE_SEARCH_PROVIDER) {
          return jsonText({
            schema: RESULT_SCHEMA,
            action,
            provider: LITERATURE_SEARCH_PROVIDER,
            tools: [
              {
                name: 'multi_source_literature_search',
                description:
                  'Search papers across Semantic Scholar, OpenAlex, arXiv, OpenReview, Crossref, and DBLP. API keys are optional; public endpoints are used when keys are absent.',
                sources: literatureSearch.defaultSources,
              },
            ],
            timestamp: Date.now(),
          });
        }
        const tools = await bioTools.listTools(domain, includeSchemas);
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'bio_tools',
          domain,
          count: tools.length,
          tools,
          timestamp: Date.now(),
        });
      }

      if (action === 'call') {
        if (provider === 'paperclip') {
          const resolvedCommand = command || String(toolArguments?.command || '');
          if (!resolvedCommand) throw new Error('research_evidence call with provider="paperclip" requires command.');
          const output = await paperclip.call(resolvedCommand);
          return jsonText({
            schema: RESULT_SCHEMA,
            action,
            provider: 'paperclip',
            mode,
            command: resolvedCommand,
            rawPreview: previewOutput(output),
            rawOutput: output,
            timestamp: Date.now(),
          });
        }
        if (!tool) throw new Error('research_evidence call with provider="bio_tools" requires tool.');
        const args = toolArguments || {};
        const result = await bioTools.callTool(tool, args);
        const output = resultText(result);
        const route: BioSearchRoute | undefined = {
          tool,
          databaseName: bioTools.toolDomain(tool) || 'bio-tools',
          domain: bioTools.toolDomain(tool) || 'bio-tools',
          sourceType: tool.includes('search_articles') ? 'paper' : 'database_record',
          buildArguments: () => args,
        };
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider: 'bio_tools',
          mode,
          tool,
          arguments: args,
          domain: bioTools.toolDomain(tool),
          rawPreview: previewOutput(output),
          rawOutput: output,
          structuredContent: result.structuredContent,
          evidenceDrafts: [buildBioEvidenceDraft({ route, tool, args, output, structured: result.structuredContent })],
          timestamp: Date.now(),
        });
      }

      if (action === 'search') {
        if (!query?.trim()) throw new Error('research_evidence search requires query.');
        const requestedSources =
          provider === LITERATURE_SEARCH_PROVIDER && !sources?.length && !source
            ? literatureSearch.defaultSources
            : sources?.length
              ? sources
              : [source || 'pmc'];
        const literatureRequested =
          provider === LITERATURE_SEARCH_PROVIDER ||
          requestedSources.some((item) => isLiteratureSearchSource(item)) ||
          (provider === 'auto' && requestedSources.some((item) => item === 'arxiv') && !paperclip.enabled);
        if (literatureRequested) {
          const literatureSources =
            provider === LITERATURE_SEARCH_PROVIDER && !sources?.length && !source
              ? literatureSearch.defaultSources
              : normalizeLiteratureSearchSources(requestedSources);
          const literature = await literatureSearch.search({
            query,
            sources: literatureSources,
            maxResults,
            startYear,
            endYear,
          });
          return jsonText({
            schema: RESULT_SCHEMA,
            action,
            provider: LITERATURE_SEARCH_PROVIDER,
            mode,
            query,
            startYear,
            endYear,
            ...buildCompactLiteratureSearchPayload(literature, maxResults),
            timestamp: Date.now(),
          });
        }
        const results = [];
        for (const item of requestedSources) {
          const bioRoute = bioToolSearchRoutes[normalizeBioSource(item)];
          const shouldUseBioTools =
            provider === 'bio_tools' ||
            (provider === 'auto' && bioRoute && !paperclip.enabled) ||
            (provider === 'auto' &&
              bioRoute &&
              !['pmc', 'abstracts', 'abstracts_only', 'arxiv', 'biorxiv', 'medrxiv'].includes(
                normalizeBioSource(item)
              ));
          if (shouldUseBioTools) {
            if (!bioRoute) {
              throw new Error(
                `No bio-tools search route is defined for source "${item}". Use action="list_tools" then action="call".`
              );
            }
            const args = bioRoute.buildArguments(query, maxResults);
            const result = await bioTools.callTool(bioRoute.tool, args);
            const output = resultText(result);
            const parsed = result.structuredContent ?? safeJsonParse(output);
            const counts = countFromStructured(parsed);
            results.push({
              provider: 'bio_tools',
              source: normalizeBioSource(item),
              tool: bioRoute.tool,
              domain: bioRoute.domain,
              found: counts.returnedCount || counts.retrievedCount || 0,
              rawPreview: previewOutput(output),
              rawOutput: output,
              structuredContent: result.structuredContent,
              evidenceDrafts: [
                buildBioEvidenceDraft({
                  route: bioRoute,
                  tool: bioRoute.tool,
                  args,
                  query,
                  output,
                  structured: parsed,
                }),
              ],
            });
            continue;
          }

          const normalizedSource = normalizeSource(item);
          const output = await paperclip.call(
            `search -s ${normalizedSource} ${JSON.stringify(query)} -n ${maxResults}`
          );
          results.push({
            provider: 'paperclip',
            source: normalizedSource,
            found: parseFoundCount(output),
            savedSearchId: parseSavedSearchId(output),
            rawPreview: previewOutput(output),
            rawOutput: output,
          });
        }
        return jsonText({
          schema: RESULT_SCHEMA,
          action,
          provider,
          mode,
          query,
          results,
          timestamp: Date.now(),
        });
      }

      const resolvedCommand =
        command ||
        (virtualPath
          ? anchor?.lineStart
            ? `cat ${JSON.stringify(virtualPath)} --lines ${anchor.lineStart}-${anchor.lineEnd || anchor.lineStart}`
            : `cat ${JSON.stringify(virtualPath)}`
          : undefined);
      if (!resolvedCommand) {
        throw new Error(
          'research_evidence read requires a PaperClip virtualPath or explicit command. Search with provider="paperclip" first; arbitrary URLs are not PaperClip read targets.'
        );
      }
      const output = await paperclip.call(resolvedCommand);
      return jsonText({
        schema: RESULT_SCHEMA,
        action,
        provider: 'paperclip',
        mode,
        sourceId,
        virtualPath,
        command: resolvedCommand,
        anchor,
        rawPreview: previewOutput(output),
        rawOutput: output,
        timestamp: Date.now(),
      });
    }
  );

  const transport = new StdioServerTransport();
  transport.onclose = closeOrigene;
  await server.connect(transport);
}

main().catch((error) => {
  console.error('[ResearchEvidenceMCP] Fatal error:', error);
  process.exit(1);
});
