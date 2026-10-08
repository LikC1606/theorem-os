/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import process from 'node:process';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { z } from 'zod';
import { installMathMcpShutdown } from "../math/mathMcpShutdown";
import { RESEARCH_EVIDENCE_ENV_KEYS } from "../common/config/researchEvidenceMcpEnv";
import { assertResearchTeamToolActionAuthorized } from "../common/types/team/researchTeamToolPolicy";
import { BUILTIN_RESEARCH_EVIDENCE_NAME } from "../common/config/builtinMcpConstants";
import {
  DEFAULT_LITERATURE_SEARCH_SOURCES,
  LITERATURE_SEARCH_PROVIDER,
  isLiteratureSearchSource,
  normalizeLiteratureSearchSources,
  searchLiterature,
} from "./literatureSearch";
import { buildCompactLiteratureSearchPayload } from "./researchEvidencePayload";

const DEFAULT_BASE_URL = 'https://paperclip.gxl.ai';
const DEFAULT_TIMEOUT_MS = 30000;
const RESULT_SCHEMA = 'deepscientist.research_evidence.result.v2';

type ProviderName = 'paperclip' | typeof LITERATURE_SEARCH_PROVIDER;

type PaperclipMcpResponse = {
  result?: {
    content?: Array<{ type?: string; text?: string }>;
  };
  error?: {
    message?: string;
  };
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

const normalizeSource = (source: string): string => (source === 'clinicaltrials' ? 'trials/us' : source);

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
      throw new Error('PaperClip is not configured. Set PAPERCLIP_API_KEY to enable it.');
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
      throw new Error('Paper search provider is disabled by the research evidence environment.');
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

async function main() {
  const paperclip = new PaperclipGateway();

  const literatureSearch = new LiteratureSearchGateway();

  const server = new McpServer({
    name: BUILTIN_RESEARCH_EVIDENCE_NAME,
    version: '1.2.0',
  });

  server.tool(
    'research_evidence',
    'Retrieve mathematical literature through public paper search or PaperClip. For PaperClip full text, search first and then read a returned virtualPath or run an explicit command; PaperClip does not read arbitrary URLs. Register sources as evidence when used in claims.',
    {
      action: z.enum(['status', 'list_tools', 'search', 'read', 'call']),
      provider: z.enum(['auto', 'paperclip', LITERATURE_SEARCH_PROVIDER]).default('auto'),
      mode: z.enum(['science', 'general']).default('science'),
      query: z.string().optional(),
      source: z
        .string()
        .optional()
        .describe('PaperClip source or public literature source, e.g. arxiv, openalex, or crossref.'),
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
      arguments: z.record(z.unknown()).optional(),
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
      arguments: toolArguments,
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
          },
          timestamp: Date.now(),
        });
      }

      if (action === 'list_tools') {
        const resolvedProvider: ProviderName =
          provider === 'paperclip' ? 'paperclip' : LITERATURE_SEARCH_PROVIDER;
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
        throw new Error('research_evidence call requires provider="paperclip". Use action="search" for paper_search.');
      }

      if (action === 'search') {
        if (!query?.trim()) throw new Error('research_evidence search requires query.');
        const requestedSources =
          (provider === LITERATURE_SEARCH_PROVIDER || (provider === 'auto' && !paperclip.enabled)) &&
          !sources?.length && !source
            ? literatureSearch.defaultSources
            : sources?.length
              ? sources
              : [source || 'pmc'];
        const literatureRequested =
          provider === LITERATURE_SEARCH_PROVIDER ||
          (provider === 'auto' && requestedSources.some((item) => isLiteratureSearchSource(item)));
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
  installMathMcpShutdown(() => server.close());

  await server.connect(transport);
}

main().catch((error) => {
  console.error('[ResearchEvidenceMCP] Fatal error:', error);
  process.exit(1);
});
