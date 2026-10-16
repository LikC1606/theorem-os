export interface ArchiveSource {
  name: string;
  path: string;
  url: string;
  sha256: string;
  lines: number;
  code: string;
}

export interface ArchiveRecord {
  id: string;
  title: string;
  subtitle: string;
  area: string;
  summary: string;
  status: 'official_accepted' | 'in_progress_not_officially_accepted';
  model: string;
  updatedAt: string;
  archiveUrl: string;
  sources: ArchiveSource[];
  declaration?: string;
  official?: {
    statementRevision: number;
    submissionUrl: string;
    resultUrl: string;
    resultBody: string;
    sourceUrl: string;
    sourceCommit: string;
    checksums: Record<string, string>;
  };
  local?: {
    status: string;
    kernelVerified: boolean;
    comparator?: string;
    receipt?: string;
    sourceProofCommit?: string;
    sourceBinding: 'matches' | 'differs' | 'unrecorded';
    axioms: string[];
    production?: {
      mode: string;
      humanDirection?: string;
      freshFromZero?: boolean;
    };
    url: string;
  };
  snapshot?: {
    runId: string;
    phase: string;
    turns: number;
    workers: number;
    taskStatuses: Record<string, number>;
  };
}

export interface ArchiveCatalog {
  schema: 'theoremos.public-archive.v1';
  repository: string;
  archiveRevision: string;
  snapshotAt: string;
  records: ArchiveRecord[];
}
