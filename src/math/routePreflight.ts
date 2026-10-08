/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import {
  canonicalMathProblemNegationPayload,
  canonicalMathProblemStatementPayloads,
  isMathRouteSelectable,
  mathRouteStructureSignatureFromNormalized,
  normalizeMathProblemContract,
  normalizeMathRouteCard,
  type MathProblemContract,
  type MathRouteCard,
  type MathRouteProbeReceipt,
} from "../common/types/team/mathematicsTeam";
import { inspectMathematicsSandboxBackends, resolveMathematicsLakePackagesCache } from "./verifier";
import { runLeanEvalLeanProbe, type LeanEvalLeanProbeResult } from "./leanEvalLeanProbe";
import { readMathematicsReceiptSecret, signMathRouteProbeReceipt } from "./receiptAttestation";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";

export type MathematicsRoutePreflightRequest = Readonly<{
  workspaceRoot: string;
  targetCommit: string;
  problemContract: MathProblemContract;
  routeCard: MathRouteCard;
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  runProbe?: (request: Parameters<typeof runLeanEvalLeanProbe>[0]) => Promise<LeanEvalLeanProbeResult>;
}>;

export type MathematicsRoutePreflightResult = Readonly<{
  status: 'passed' | 'failed' | 'unavailable' | 'invalid';
  cacheKey: string;
  cacheHit: boolean;
  diagnostics: string;
  receipt?: MathRouteProbeReceipt;
}>;

const sha256 = (value: string | Uint8Array): string => crypto.createHash('sha256').update(value).digest('hex');
const ENVIRONMENT_FILES = Object.freeze(['lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean']);
const ENVIRONMENT_VARIABLES = Object.freeze([
  'PATH',
  'ELAN_HOME',
  'LAKE_HOME',
  'LEAN_PATH',
  'LEAN_SYSROOT',
  'DEEPSCIENTIST_MATH_SANDBOX_BACKEND',
  'DEEPSCIENTIST_MATH_SANDBOX_IMAGE',
]);
const MAX_CACHE_ENTRIES = 128;
const preflightCache = new Map<string, MathematicsRoutePreflightResult>();
const preflightInflight = new Map<string, Promise<MathematicsRoutePreflightResult>>();
const FULL_OID = /^[0-9a-f]{40,64}$/iu;

const invalidRequestResult = (
  request: MathematicsRoutePreflightRequest,
  diagnostics: string
): MathematicsRoutePreflightResult =>
  Object.freeze({
    status: 'invalid',
    cacheKey: sha256(
      JSON.stringify({
        schema: 'deepscientist.mathematics.route-preflight-invalid.v1',
        workspaceRoot: String(request.workspaceRoot || ''),
        targetCommit: String(request.targetCommit || ''),
        statementHash: String(request.problemContract?.statementHash || ''),
        routeFingerprint: String(request.routeCard?.routeFingerprint || ''),
        diagnostics,
      })
    ),
    cacheHit: false,
    diagnostics,
  });

const fileIdentity = (root: string, relative: string): readonly [string, string | null] => {
  try {
    const file = path.join(root, relative);
    const stat = fs.lstatSync(file);
    return Object.freeze([relative, stat.isFile() && !stat.isSymbolicLink() ? sha256(fs.readFileSync(file)) : null]);
  } catch {
    return Object.freeze([relative, null]);
  }
};

/**
 * Bind a preflight to the source contents that Lean can see in its workspace.
 *
 * The target commit alone is insufficient here: callers may use a worktree
 * with an uncommitted source edit (or a scratch directory without Git
 * metadata).  Git gives us a bounded, authoritative file list for normal
 * worktrees, while the recursive fallback keeps test/scratch workspaces
 * content-bound as well.  Generated probe and Lake output are intentionally
 * excluded because they are owned by the verifier and are represented by the
 * separate package/environment identities below.
 */
const workspaceContentIdentity = (workspaceRoot: string): unknown => {
  const git = spawnSync('git', ['-C', workspaceRoot, 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], {
    encoding: 'buffer',
    maxBuffer: 16 * 1024 * 1024,
  });
  let relativeFiles: string[];
  if (git.status === 0 && !git.error) {
    relativeFiles = Buffer.from(git.stdout ?? '')
      .toString('utf8')
      .split('\0')
      .filter(Boolean)
      .map((file) => file.split(path.sep).join('/'));
  } else {
    relativeFiles = [];
    const visit = (directory: string): void => {
      for (const entry of fs
        .readdirSync(directory, { withFileTypes: true })
        .toSorted((a, b) => a.name.localeCompare(b.name))) {
        if (entry.name === '.git' || entry.name === '.lake' || entry.name === '.deepscientist') continue;
        const absolute = path.join(directory, entry.name);
        const relative = path.relative(workspaceRoot, absolute).split(path.sep).join('/');
        if (entry.isDirectory()) visit(absolute);
        else relativeFiles.push(relative);
      }
    };
    visit(workspaceRoot);
  }
  return relativeFiles.toSorted().map((relative) => {
    const absolute = path.join(workspaceRoot, relative);
    try {
      const stat = fs.lstatSync(absolute);
      if (stat.isFile() && !stat.isSymbolicLink()) return [relative, 'file', sha256(fs.readFileSync(absolute))];
      if (stat.isSymbolicLink()) return [relative, 'symlink', sha256(`symlink\0${fs.readlinkSync(absolute)}`)];
      return [relative, stat.isDirectory() ? 'directory' : 'other', null];
    } catch {
      return [relative, 'missing', null];
    }
  });
};

const packageCacheIdentity = (workspaceRoot: string, lakePackagesPath?: string): unknown => {
  const candidate = lakePackagesPath || path.join(workspaceRoot, '.lake', 'packages');
  try {
    const stat = fs.lstatSync(candidate);
    if (!stat.isDirectory() || stat.isSymbolicLink()) return { available: false };
    return {
      available: true,
      path: fs.realpathSync(candidate),
      packages: fs
        .readdirSync(candidate, { withFileTypes: true })
        .filter((entry) => entry.isDirectory())
        .map((entry) => entry.name)
        .toSorted(),
      contentSha256: sha256(JSON.stringify(workspaceContentIdentity(candidate))),
    };
  } catch {
    return { available: false };
  }
};

/** If the workspace is a Git checkout, bind the probe to the exact revision
 * named by the assignment. Test-only scratch directories without Git metadata
 * remain usable with an injected probe implementation. */
const assertWorkspaceTargetCommit = (workspaceRoot: string, targetCommit: string): void => {
  if (!FULL_OID.test(targetCommit.trim())) throw new Error('Mathematics route-preflight targetCommit is invalid');
  const gitMetadata = path.join(workspaceRoot, '.git');
  try {
    const metadataStat = fs.lstatSync(gitMetadata);
    if (metadataStat.isSymbolicLink()) {
      throw new Error('Mathematics route-preflight workspace Git metadata cannot be a symbolic link');
    }
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return;
    throw error;
  }
  const result = spawnSync('git', ['-C', workspaceRoot, 'rev-parse', 'HEAD'], {
    encoding: 'utf8',
    maxBuffer: 1024,
  });
  if (result.status !== 0) throw new Error('Mathematics route-preflight workspace Git revision is unavailable');
  const head = result.stdout.trim().toLowerCase();
  if (head !== targetCommit.trim().toLowerCase()) {
    throw new Error('Mathematics route-preflight workspace HEAD does not match targetCommit');
  }
};

const environmentFingerprint = (workspaceRoot: string, env: NodeJS.ProcessEnv, lakePackagesPath?: string): string => {
  const sandbox = inspectMathematicsSandboxBackends(env);
  return sha256(
    JSON.stringify({
      schema: 'deepscientist.mathematics.route-preflight-environment.v2',
      platform: process.platform,
      arch: process.arch,
      node: process.version,
      projectFiles: ENVIRONMENT_FILES.map((file) => fileIdentity(workspaceRoot, file)),
      workspaceContent: workspaceContentIdentity(workspaceRoot),
      packageCache: packageCacheIdentity(workspaceRoot, lakePackagesPath),
      sandbox: { available: sandbox.available, preferred: sandbox.preferred ?? null },
      environment: Object.fromEntries(ENVIRONMENT_VARIABLES.map((name) => [name, env[name] ?? ''])),
    })
  );
};

/** Compute the runtime identity used to bind a persisted route probe receipt. */
export const mathematicsRoutePreflightEnvironmentFingerprint = (
  workspaceRoot: string,
  sourceEnv: NodeJS.ProcessEnv = process.env,
  lakePackagesPath?: string
): string => {
  const resolvedWorkspaceRoot = fs.realpathSync(path.resolve(workspaceRoot));
  const env = resolveMathematicsRuntimeEnvironment(sourceEnv);
  const packagesPath = lakePackagesPath ?? resolveMathematicsLakePackagesCache(resolvedWorkspaceRoot, env);
  return environmentFingerprint(resolvedWorkspaceRoot, env, packagesPath);
};

type LeanDeclaration = Readonly<{
  keyword: 'theorem' | 'lemma' | 'def' | 'abbrev' | 'opaque';
  name: string;
  signature: string;
}>;

const declarationSignature = (source: string): LeanDeclaration => {
  const trimmed = source.trim();
  const match =
    /^(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|opaque)\s+([\p{L}\p{M}\p{N}_'.]+)([\s\S]*)$/u.exec(
      trimmed
    );
  if (!match) {
    throw new Error('Route plan nodes must use an exact theorem, lemma, or explicitly typed definition declaration');
  }
  const body = /\s*:=\s*[\s\S]*$/u.exec(match[3]);
  const signature = (body ? match[3].slice(0, body.index) : match[3]).trimEnd();
  if (!signature.includes(':')) throw new Error(`Route declaration ${match[2]} is missing its result type`);
  return Object.freeze({
    keyword: match[1] as LeanDeclaration['keyword'],
    name: match[2],
    signature,
  });
};

const proofBody = (skeleton: string): string => {
  const trimmed = skeleton.trim();
  if (/^by(?:\s|$)/u.test(trimmed)) return trimmed;
  const declarationBody = /:=\s*(by\b[\s\S]*)$/u.exec(trimmed)?.[1];
  if (declarationBody) return declarationBody.trim();
  throw new Error('Route premiseBundle.leanSkeleton must be an executable `by` proof');
};

const topologicalNodes = (card: MathRouteCard): readonly MathRouteCard['planNodes'][number][] => {
  const byId = new Map(card.planNodes.map((node) => [node.id, node]));
  const visited = new Set<string>();
  const ordered: MathRouteCard['planNodes'][number][] = [];
  const visit = (id: string): void => {
    if (visited.has(id)) return;
    const node = byId.get(id);
    if (!node) throw new Error(`Route plan dependency ${id} is missing`);
    visited.add(id);
    for (const dependency of node.dependsOn) visit(dependency);
    ordered.push(node);
  };
  visit(card.rootNodeId);
  return Object.freeze(ordered);
};

const openedNamespaces = (formalStatement: string): string => {
  const namespaces = [...formalStatement.matchAll(/^\s*namespace\s+([\p{L}\p{M}\p{N}_'.]+)\s*$/gmu)].map(
    (match) => match[1]
  );
  return [...new Set(namespaces)].map((name) => `open ${name}`).join('\n');
};

/** Build a disposable harness for speculative route composition with explicit dependency placeholders. */
export function createMathematicsRoutePreflightHarness(
  problemContract: MathProblemContract,
  routeCardInput: MathRouteCard
): string {
  const card = normalizeMathRouteCard(routeCardInput);
  if (!isMathRouteSelectable(card)) {
    throw new Error('Route must pass every semantic viability check before runtime preflight');
  }
  const ordered = topologicalNodes(card);
  const root = ordered.at(-1);
  if (!root || root.id !== card.rootNodeId) throw new Error('Route root is not reachable from its dependency DAG');
  const rootDeclaration = declarationSignature(root.provisionalLeanStatement);
  if (!['theorem', 'lemma'].includes(rootDeclaration.keyword)) {
    throw new Error('Route root must be a theorem or lemma declaration');
  }
  const body = proofBody(card.premiseBundle.leanSkeleton);
  const rootName = rootDeclaration.name.split('.').at(-1)!;
  if (new RegExp(`\\b${rootName.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&')}\\b`, 'u').test(body)) {
    throw new Error('Route closure skeleton must not invoke the target theorem recursively');
  }
  const structureHash = mathRouteStructureSignatureFromNormalized(card).slice(0, 16);
  const namespace = `DeepScientistRoutePreflight_${structureHash}`;
  const assumptions = ordered
    .slice(0, -1)
    .map((node) => {
      const declaration = declarationSignature(node.provisionalLeanStatement);
      return `axiom ${declaration.name}${declaration.signature}`;
    })
    .join('\n\n');
  const opens = openedNamespaces(problemContract.formalStatement);
  return [
    problemContract.formalStatement.trimEnd(),
    '',
    `namespace ${namespace}`,
    opens,
    assumptions,
    `${rootDeclaration.keyword} ${rootDeclaration.name}${rootDeclaration.signature} := ${body}`,
    `end ${namespace}`,
    '',
  ]
    .filter((part, index, values) => part || (index > 0 && values[index - 1]))
    .join('\n');
}

const rememberResult = (cacheKey: string, result: MathematicsRoutePreflightResult): void => {
  preflightCache.set(cacheKey, result);
  while (preflightCache.size > MAX_CACHE_ENTRIES) {
    const oldest = preflightCache.keys().next().value;
    if (!oldest) break;
    preflightCache.delete(oldest);
  }
};

/** Run one verifier-owned preflight before any Formalizer worktree or Core turn is created. */
export async function runMathematicsRoutePreflight(
  request: MathematicsRoutePreflightRequest
): Promise<MathematicsRoutePreflightResult> {
  let workspaceRoot: string;
  try {
    workspaceRoot = fs.realpathSync(path.resolve(request.workspaceRoot));
    if (!fs.statSync(workspaceRoot).isDirectory()) {
      return invalidRequestResult(request, 'Mathematics route-preflight workspace must be a directory');
    }
  } catch (error) {
    return invalidRequestResult(
      request,
      `Mathematics route-preflight workspace is unavailable: ${error instanceof Error ? error.message : String(error)}`
    );
  }
  let card: MathRouteCard;
  try {
    card = normalizeMathRouteCard(request.routeCard);
  } catch (error) {
    return invalidRequestResult(
      request,
      `Mathematics route-preflight route is invalid: ${error instanceof Error ? error.message : String(error)}`
    );
  }
  let problemContract: MathProblemContract;
  try {
    problemContract = normalizeMathProblemContract(request.problemContract);
    const payloads = canonicalMathProblemStatementPayloads(problemContract);
    if (
      sha256(payloads.informal) !== problemContract.statementHash ||
      sha256(payloads.lean) !== problemContract.leanStatementHash
    ) {
      throw new Error('Mathematics route-preflight problem statement hashes are not canonical');
    }
    const negationPayload = canonicalMathProblemNegationPayload(problemContract);
    if (negationPayload && sha256(negationPayload) !== problemContract.leanNegationHash) {
      throw new Error('Mathematics route-preflight negation hash is not canonical');
    }
    if (card.statementHash !== problemContract.statementHash) {
      throw new Error('Mathematics route-preflight route statementHash does not match problemContract');
    }
    assertWorkspaceTargetCommit(workspaceRoot, request.targetCommit);
  } catch (error) {
    const diagnostics = error instanceof Error ? error.message : String(error);
    return invalidRequestResult(request, diagnostics);
  }
  // Keep this binding compatible with the runtime receipt contract; the
  // canonical payload hashes above are the identity checks, while sourceHash
  // identifies the exact formal source text used by the harness.
  const sourceHash = sha256(problemContract.formalStatement);
  const routeStructureHash = sha256(mathRouteStructureSignatureFromNormalized(card));
  const env = resolveMathematicsRuntimeEnvironment(request.env ?? process.env);
  const lakePackagesPath = request.lakePackagesPath ?? resolveMathematicsLakePackagesCache(workspaceRoot, env);
  const executionEnvironment = environmentFingerprint(workspaceRoot, env, lakePackagesPath);
  let harness: string;
  try {
    harness = createMathematicsRoutePreflightHarness(problemContract, card);
  } catch (error) {
    const diagnostics = error instanceof Error ? error.message : String(error);
    return Object.freeze({
      status: 'invalid',
      cacheKey: sha256(`${request.targetCommit}\0${sourceHash}\0${routeStructureHash}\0${executionEnvironment}`),
      cacheHit: false,
      diagnostics,
    });
  }
  const harnessHash = sha256(harness);
  const secret = readMathematicsReceiptSecret();
  if (!secret) {
    return Object.freeze({
      status: 'unavailable',
      cacheKey: sha256(`${workspaceRoot}\0${request.targetCommit}\0${harnessHash}\0${executionEnvironment}`),
      cacheHit: false,
      diagnostics: 'Mathematics route-preflight receipt key is unavailable',
    });
  }
  const receiptKeyId = sha256(secret).slice(0, 16);
  const cacheKey = sha256(
    JSON.stringify({
      schema: 'deepscientist.mathematics.route-preflight-cache.v1',
      workspaceRoot,
      statementHash: request.problemContract.statementHash,
      targetCommit: request.targetCommit,
      routeFingerprint: card.routeFingerprint,
      routeStructureHash,
      sourceHash,
      harnessHash,
      environmentFingerprint: executionEnvironment,
      receiptKeyId,
    })
  );
  const cached = preflightCache.get(cacheKey);
  if (cached) return Object.freeze({ ...cached, cacheHit: true });

  const active = preflightInflight.get(cacheKey);
  if (active) {
    const result = await active;
    return Object.freeze({ ...result, cacheHit: true });
  }
  const pending = (async (): Promise<MathematicsRoutePreflightResult> => {
    let probe: LeanEvalLeanProbeResult;
    try {
      probe = await (request.runProbe ?? runLeanEvalLeanProbe)({
        workspaceRoot,
        sourceFile: `.deepscientist/math/route-preflight/${cacheKey}.lean`,
        sourceText: harness,
        mode: 'compile',
        timeoutMs: request.timeoutMs ?? 45_000,
        signal: request.signal,
        env,
        ...(lakePackagesPath ? { lakePackagesPath } : {}),
      });
    } catch (error) {
      return Object.freeze({
        status: 'unavailable',
        cacheKey,
        cacheHit: false,
        diagnostics: error instanceof Error ? error.message : String(error),
      });
    }
    if (probe.status !== 'passed') {
      const result = Object.freeze({
        status: probe.status,
        cacheKey,
        cacheHit: false,
        diagnostics: probe.error || probe.diagnostics || 'Lean route preflight did not pass',
      });
      if (probe.status === 'failed') rememberResult(cacheKey, result);
      return result;
    }
    const assessorSessionId = `runtime:lean-route-preflight:${executionEnvironment.slice(0, 16)}`;
    const receipt = signMathRouteProbeReceipt(
      {
        statementHash: request.problemContract.statementHash,
        routeFingerprint: card.routeFingerprint,
        routeBrief: {
          routeFingerprint: card.routeFingerprint,
          structuralCommitment: card.structuralCommitment,
          decisiveLemma: card.decisiveLemma,
          decisiveTest: card.decisiveTest,
          falsificationSignal: card.falsificationSignal,
          expectedInformationGain: card.expectedInformationGain,
          estimatedCost: card.estimatedCost,
          formalizationRisk: card.formalizationRisk,
        },
        proposerSessionId: card.proposerSessionId,
        assessorSessionId,
        outcome: 'supported',
        verificationMode: 'speculative_axiom_closure',
        probeSummary:
          'The selected route DAG and terminal Lean skeleton compose against axiom placeholders; dependencies remain unverified.',
        evidenceRefs: [`lean-route-preflight:${probe.proofStateFingerprint}`],
        checkedAt: Date.now(),
        proposalDeliveryId: `route-card:${routeStructureHash}`,
        assessmentDeliveryId: `runtime-route-preflight:${cacheKey}`,
        runtimeBinding: {
          targetCommit: request.targetCommit,
          routeStructureHash,
          sourceHash,
          harnessHash,
          environmentFingerprint: executionEnvironment,
          proofStateFingerprint: probe.proofStateFingerprint,
          durationMs: probe.durationMs,
          ...(probe.sandboxBackend ? { sandboxBackend: probe.sandboxBackend } : {}),
        },
      },
      secret
    );
    const result = Object.freeze({ status: 'passed' as const, cacheKey, cacheHit: false, diagnostics: '', receipt });
    rememberResult(cacheKey, result);
    return result;
  })();
  preflightInflight.set(cacheKey, pending);
  try {
    return await pending;
  } finally {
    if (preflightInflight.get(cacheKey) === pending) preflightInflight.delete(cacheKey);
  }
}
