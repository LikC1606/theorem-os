export type WebEffort = 'low' | 'medium' | 'high' | 'xhigh';
export type WebCoordination = 'cooperative' | 'independent';
export type WebRunStatus = 'queued' | 'running' | 'completed' | 'cancelled' | 'error';
export type WebEnvironment = 'standard' | 'mathlib';

export type WebProvider = { id: string; name: string; baseUrl: string };
export type WebEnvironmentOption = { id: WebEnvironment; name: string; description: string;
  toolchain: string; mathlibRevision?: string };
export type WebTemplate = { id: string; name: string; environment: WebEnvironment; source: string; task: string };
export type WebRunInput = {
  providerId: string;
  apiKey: string;
  model: string;
  effort: WebEffort;
  environment?: WebEnvironment;
  source: string;
  task: string;
  maxTurns: number;
  maxRunSeconds: number;
  workers: number;
  coordination: WebCoordination;
};
export type WebEvent = { sequence: number; at: string; type: string; message: string };
export type WebResult = {
  status: string;
  proof: string;
  report: Record<string, unknown>;
};
export type WebRun = {
  id: string;
  title: string;
  status: WebRunStatus;
  phase: string;
  createdAt: string;
  updatedAt: string;
  finishedAt?: string;
  timings?: { preparing?: string; solving?: string; evaluating?: string };
  providerId: string;
  model: string;
  effort: WebEffort;
  environment: WebEnvironment;
  source: string;
  task: string;
  maxTurns: number;
  maxRunSeconds: number;
  workers: number;
  coordination: WebCoordination;
  events: WebEvent[];
  result?: WebResult;
  error?: string;
};
export type WebSession = {
  csrfToken: string;
  providers: WebProvider[];
  environments: WebEnvironmentOption[];
  templates: WebTemplate[];
  defaults: Pick<WebRunInput, 'model' | 'effort' | 'maxTurns' | 'maxRunSeconds' | 'workers' | 'coordination'> & { environment: WebEnvironment };
  limits: { maxTurns: number; maxRunSeconds: number; maxWorkers: number; maxSourceBytes: number; maxTaskBytes: number };
  runtime: { ready: boolean; message: string };
};
export type WorkerInput = { id: string; input: WebRunInput; provider: WebProvider };
export type WorkerMessage =
  | { type: 'progress'; event: string; message: string }
  | { type: 'result'; result: WebResult }
  | { type: 'error'; message: string };
