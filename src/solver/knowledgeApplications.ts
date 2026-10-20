import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathArtifactCurrent, mathDigest, readMathFile } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { limitMathOutput } from '../math/mathProcess';
import { leanDiagnosticEnvironmentIdentity } from '../math/leanResidualGoals';
import { LAKE_CONFIGURATION_FILES as configurationFiles, mathLocalModuleBuildOrder } from '../math/mathConstructionSources';
import { checkLeanType } from '../math/leanTypeDiagnostics';
import type { ContextSection } from './contextCompiler';
import type { KnowledgeApplicationCheck, KnowledgeUse } from './knowledgeUsage';
import { proofReuseEnvironment } from './proofReuse';
import { isAdvisoryTask, taskVersion, type CooperativeTask } from './tasks';

type Inputs = {
  projectRoot: string; env: NodeJS.ProcessEnv; environmentDigest: string; commit: string; task: CooperativeTask;
  originalContexts?: readonly { proofPath: string; theoremName: string }[];
  sourceAtCommit: (file: string) => string; signal?: AbortSignal; timeoutMs: number;
  previous?: readonly KnowledgeUse[];
};

function filesCurrent(projectRoot: string, check: KnowledgeApplicationCheck, contextFile: string): boolean {
  try {
    const currentFiles = [...mathLocalModuleBuildOrder(projectRoot, contextFile).map(module => module.file),
      ...configurationFiles.filter(file => fs.existsSync(path.join(projectRoot, file)))];
    return !!check.files?.length && canonicalMathJson(currentFiles) === canonicalMathJson(check.files.map(item => item.file)) && check.files.every(item => {
      const file = path.resolve(projectRoot, item.file);
      if (path.isAbsolute(item.file) || !isMathPathWithin(projectRoot, file)) return false;
      assertMathCanonicalPath(file);
      return mathDigest(readMathFile(file, 4_000_000).bytes) === item.digest;
    });
  } catch { return false; }
}

function checkCurrent(projectRoot: string, env: NodeJS.ProcessEnv, environmentDigest: string, check: KnowledgeApplicationCheck, contextFile: string) {
  try {
    const environment = proofReuseEnvironment(projectRoot, env);
    if (check.environmentDigest !== environmentDigest || !check.toolIdentity || !filesCurrent(projectRoot, check, contextFile) ||
        !environment.reusable || !environment.digest || environment.digest !== check.reuseEnvironmentDigest) return false;
    const identity = leanDiagnosticEnvironmentIdentity(projectRoot, env);
    return identity.environmentDigest === check.diagnosticEnvironmentDigest && identity.toolIdentity === check.toolIdentity;
  } catch { return false; }
}

function submittedSnapshot(files: KnowledgeApplicationCheck['files'], input: Inputs) {
  try {
    return !!files?.length && files.every(file => file.file === '.lake/package-overrides.json' ||
      mathDigest(input.sourceAtCommit(file.file)) === file.digest);
  } catch { return false; }
}

/** Only explicitly selected expressions are examined. Errors in optional experience never reject a proof. */
export async function checkKnowledgeApplications(uses: readonly KnowledgeUse[], input: Inputs): Promise<KnowledgeUse[]> {
  let checkedCount = 0;
  const output: KnowledgeUse[] = [];
  for (const use of uses) {
    if (!use.application) { output.push(use); continue; }
    const { check: _untrusted, ...report } = use.application;
    const base: KnowledgeApplicationCheck = { status: 'unavailable', reason: 'application-check-unavailable',
      authority: 'advisory-application-elaboration', proofAcceptance: 'not-assessed', consumerCoverage: 'not-assessed',
      commit: input.commit, environmentDigest: input.environmentDigest };
    const append = (check: KnowledgeApplicationCheck) => output.push({ ...use, application: { ...report, check } });
    if (use.consumer.taskId !== input.task.id || use.consumer.taskDigest !== taskVersion(input.task)) {
      append({ ...base, reason: 'consumer-contract-changed' }); continue;
    }
    const contextAllowed = input.task.proofPath === report.context.file && input.task.theoremName === report.context.declaration ||
      isAdvisoryTask(input.task) && input.originalContexts?.some(target =>
        target.proofPath === report.context.file && target.theoremName === report.context.declaration);
    if (!contextAllowed) { append({ ...base, reason: 'application-context-not-assigned' }); continue; }
    if (checkedCount >= 4) { append({ ...base, reason: 'selected-application-check-budget' }); continue; }
    try {
      const environment = proofReuseEnvironment(input.projectRoot, input.env);
      if (!environment.reusable) { append({ ...base, reason: 'application-environment-not-frozen' }); continue; }
      const prior = input.previous?.find(previous => previous.id === use.id && previous.catalogDigest === use.catalogDigest &&
        canonicalMathJson(previous.consumer) === canonicalMathJson(use.consumer) &&
        canonicalMathJson(previous.declaration) === canonicalMathJson(use.declaration) && previous.application &&
        canonicalMathJson({ ...previous.application, check: undefined }) === canonicalMathJson(report) &&
        ['elaborated', 'failed'].includes(previous.application.check?.status ?? '') &&
        checkCurrent(input.projectRoot, environment.env, input.environmentDigest, previous.application.check!, report.context.file) &&
        submittedSnapshot(previous.application.check!.files, input) &&
        mathArtifactCurrent(input.projectRoot, previous.application.check!.artifact));
      if (prior?.application?.check) { append({ ...prior.application.check, reused: true }); continue; }
      checkedCount++;
      input.signal?.throwIfAborted();
      const result = await checkLeanType({ projectRoot: input.projectRoot, file: report.context.file,
        context: report.context.declaration, type: report.expectedType, expression: report.expression,
        env: environment.env, signal: input.signal, timeoutMs: input.timeoutMs });
      // The host records only the exact submitted source snapshot, never a later live edit.
      if (input.signal?.aborted || !submittedSnapshot(result.sourceFiles, input)) {
        append({ ...base, reason: 'application-source-not-submitted-snapshot' }); continue;
      }
      const complete = result.status === 'elaborated';
      append({ ...base, status: complete ? 'elaborated' : result.exitCode === 1 && !result.timedOut ? 'failed' : 'unavailable',
        reason: complete ? 'selected-expression-elaborated-against-requested-type' : 'selected-expression-did-not-elaborate',
        sourceSnapshotDigest: result.sourceSnapshotDigest, projectionDigest: result.projectionDigest,
        reuseEnvironmentDigest: environment.digest,
        diagnosticEnvironmentDigest: result.environment.environmentDigest, toolIdentity: result.environment.toolIdentity,
        files: result.sourceFiles, artifact: result.artifact, elaboratedType: result.type,
        ...(complete ? { selectedDeclarationUsed: result.constants?.includes(use.declaration.name.replace(/^_root_\./u, '')) ?? false } : {}),
        ...(result.firstBlocking || !complete ? { diagnostic: limitMathOutput(result.firstBlocking?.message || result.stderr || result.stdout,
          8000, 'head') } : {}) });
    } catch (error) {
      append({ ...base, reason: input.signal?.aborted ? 'application-check-aborted' :
        limitMathOutput(error instanceof Error ? error.message : 'application-check-unavailable', 1000, 'head') });
    }
  }
  return output;
}

/** Scoped experience is recalled alongside findings. Historical success always requires a fresh current check. */
export function knowledgeApplicationContextSections(input: {
  uses: readonly KnowledgeUse[]; projectRoot: string; env: NodeJS.ProcessEnv; environmentDigest: string;
  catalogDigest: string; tasks: readonly CooperativeTask[];
}): ContextSection[] {
  const entries = [...new Map(input.uses.filter(use => use.application && use.catalogDigest === input.catalogDigest)
    .map(use => [mathDigest(canonicalMathJson(use)), use])).values()].reverse().slice(0, 4);
  return entries.map(use => {
    const application = use.application!, check = application.check;
    const current = check && input.tasks.some(task => task.id === use.consumer.taskId && taskVersion(task) === use.consumer.taskDigest) &&
      checkCurrent(input.projectRoot, input.env, input.environmentDigest, check, application.context.file);
    const fullDigest = mathDigest(canonicalMathJson(use));
    const packet = { evidence: 'scoped-advisory-application-experience', proofAcceptance: 'not-assessed', requiresFreshCheck: true,
      scopeStatus: current ? 'current-inputs' : 'historical-or-unchecked-inputs', id: use.id, consumer: use.consumer,
      declaration: use.declaration, complete: true, application,
      read: { file: 'COOPERATION.json', collection: 'deliveries[].knowledgeUses', digest: fullDigest } };
    let text = JSON.stringify(packet);
    if (Buffer.byteLength(text) > 6000) {
      const preview = limitMathOutput(JSON.stringify(application), 3000, 'head');
      text = JSON.stringify({ ...packet, complete: false, application: { preview, complete: false,
        bytes: Buffer.byteLength(JSON.stringify(application)), check: check && { status: check.status, reason: check.reason,
          artifact: check.artifact, selectedDeclarationUsed: check.selectedDeclarationUsed } } });
    }
    // Direct and cooperative workers can read a complete local copy without another model or Lean call.
    try {
      const directory = path.join(input.projectRoot, '.lake', 'knowledge-applications');
      assertMathCanonicalPath(directory); fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
      const file = path.join(directory, `${fullDigest}.json`);
      assertMathCanonicalPath(file); fs.writeFileSync(file, canonicalMathJson(use), { mode: 0o600 });
      text += '\nFull recorded adaptation: ' + path.relative(input.projectRoot, file).replaceAll(path.sep, '/') + ' sha256=' + fullDigest;
    } catch { /* The scoped archive/delivery remains the full record when local scratch is unavailable. */ }
    return { id: `knowledge-application:${fullDigest}`, kind: 'sources', text, priority: 8 };
  });
}
