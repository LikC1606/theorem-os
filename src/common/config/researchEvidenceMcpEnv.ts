/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export const RESEARCH_EVIDENCE_ENV_KEYS = {
  apiKey: 'PAPERCLIP_API_KEY',
  paperclipEnabled: 'PAPERCLIP_ENABLED',
  baseUrl: 'PAPERCLIP_BASE_URL',
  timeoutMs: 'PAPERCLIP_TIMEOUT_MS',
  literatureSearchEnabled: 'DEEPSCIENTIST_LITERATURE_SEARCH_ENABLED',
  literatureSearchDefaultSources: 'DEEPSCIENTIST_LITERATURE_SEARCH_SOURCES',
  semanticScholarApiKey: 'SEMANTIC_SCHOLAR_API_KEY',
  openAlexApiKey: 'OPENALEX_API_KEY',
  openAlexEmail: 'OPENALEX_EMAIL',
  crossrefEmail: 'CROSSREF_MAILTO',
  crossrefApiToken: 'CROSSREF_API_TOKEN',
} as const;
