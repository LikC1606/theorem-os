/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import {
  MATH_EVIDENCE_DELTA_KINDS,
  MATH_FAILURE_CATEGORIES,
  MATH_INFRA_STATUSES,
  MATH_ROUTE_DISPOSITIONS,
  classifyMathProgress,
  classifyMathProgressKind,
  mathActionablePlanSchedule,
  mathActionablePlanScheduleFromNormalized,
  mathRouteStructureSignatureFromNormalized,
  mathCandidateReviewAction,
  normalizeMathPlanExpansion,
  type MathFailureLedger,
  type MathFailureCategory,
  type MathLesson,
  type MathLocalGateReceipt,
  type MathSourceProgress,
  type MathPlanNode,
  type MathPlanSnapshot,
  type MathActiveNodeProofPack,
  type MathRouteCard,
  type MathProofState,
  type MathResearchFinding,
} from "../common/types/team/mathematicsTeam";
import { deriveMathematicsMechanismCapsules, type MathematicsPortfolio } from "../common/chat/mathematics";
import {
  RESEARCH_TEAM_RESULT_SCHEMA,
  type ResearchTeamAssignment,
  type ResearchTeamAssignmentBinding,
  type ResearchTeamResult,
} from "../common/types/team/researchTeamContracts";
import type {
  ProjectGitResearchTeamAssignmentReceipt,
  ProjectGitResolveCommitRequest,
} from "../project-git/index";
import type { ResearchTeamToolCapability } from "./toolCapability";
import { createMathematicsWorkerResultContract, normalizeMathematicsWorkerAction } from "./researchTeamResultContract";
import { deriveLeanProofFrontier } from "../math/leanProofFrontier";
import { readMathResearchWorkflowState } from "../math/mathResearchWorkflow";
import { isMathLiteRunEnvironment } from "../math/mathRunInputs";
import { canonicalMathJson, mathDigest } from "../math/mathRuntimeIo";

type ResearchTeamRosterMember = ResearchTeamToolCapability['roster'][number];
type DurableAssignmentValidator = (
  value: Record<string, unknown> | ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember
) => ResearchTeamAssignment;
type AssignmentReader = (request: {
  workspace: string;
  teamId: string;
  slotId: string;
  assignmentId: string;
}) => ProjectGitResearchTeamAssignmentReceipt | undefined;
type PreparedCommitResolver = (request: ProjectGitResolveCommitRequest) => string;

const FULL_GIT_OBJECT_ID = /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u;
const SHORT_GIT_OBJECT_ID = /^[a-f0-9]{4,63}$/u;

const LEAN_SOURCE_DECLARATION_PATTERN =
  /^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|opaque|abbrev|example|instance|class|structure|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)/gmu;
const LEAN_SOURCE_ESCAPE_PATTERN = /\b(?:sorry|admit|native_decide)\b|\baxiom\s+[A-Za-z_][A-Za-z0-9_']*/gu;

/** Remove Lean comments while preserving strings and declaration line layout. */
function stripLeanCommentsForSourceIdentity(source: string): string {
  let output = '';
  let blockDepth = 0;
  let lineComment = false;
  let stringLiteral = false;
  let escaped = false;
  for (let index = 0; index < source.length; index += 1) {
    const current = source[index]!;
    const next = source[index + 1];
    if (lineComment) {
      if (current === '\n') {
        lineComment = false;
        output += current;
      } else {
        output += ' ';
      }
      continue;
    }
    if (blockDepth > 0) {
      if (current === '/' && next === '*') {
        blockDepth += 1;
        output += '  ';
        index += 1;
      } else if (current === '*' && next === '/') {
        blockDepth -= 1;
        output += '  ';
        index += 1;
      } else {
        output += current === '\n' ? '\n' : ' ';
      }
      continue;
    }
    if (stringLiteral) {
      output += current;
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === '"') stringLiteral = false;
      continue;
    }
    if (current === '"') {
      stringLiteral = true;
      output += current;
    } else if (current === '-' && next === '-') {
      lineComment = true;
      output += '  ';
      index += 1;
    } else if (current === '/' && next === '*') {
      blockDepth = 1;
      output += '  ';
      index += 1;
    } else {
      output += current;
    }
  }
  return output;
}

function normalizeLeanSourceIdentity(source: string): string {
  return stripLeanCommentsForSourceIdentity(source).replace(/\s+/gu, ' ').trim();
}

function leanSourceEscapeCount(source: string): number {
  const withoutStrings = stripLeanCommentsForSourceIdentity(source).replace(/"(?:\\.|[^"\\])*"/gu, ' ');
  return [...withoutStrings.matchAll(LEAN_SOURCE_ESCAPE_PATTERN)].length;
}

function sourceDeclarationSlices(source: string): ReadonlyMap<string, { name: string; body: string }> {
  const layout = stripLeanCommentsForSourceIdentity(source);
  const matches = [...layout.matchAll(LEAN_SOURCE_DECLARATION_PATTERN)];
  const occurrences = new Map<string, number>();
  const slices = new Map<string, { name: string; body: string }>();
  matches.forEach((match, index) => {
    const name = match[1]!;
    const occurrence = occurrences.get(name) ?? 0;
    occurrences.set(name, occurrence + 1);
    const start = match.index ?? 0;
    const end = matches[index + 1]?.index ?? layout.length;
    slices.set(`${name}\u0000${occurrence}`, {
      name,
      body: normalizeLeanSourceIdentity(layout.slice(start, end)),
    });
  });
  return slices;
}

function projectRelativeLeanArtifactPathForSource(candidate: unknown): string | undefined {
  if (typeof candidate !== 'string') return undefined;
  const normalized = candidate.trim().replaceAll('\\', '/');
  const selector = normalized.indexOf('#');
  const filePath = (selector >= 0 ? normalized.slice(0, selector) : normalized).trim();
  if (!filePath || pathIsAbsolute(filePath) || filePath.split('/').includes('..')) return undefined;
  if (!filePath.toLowerCase().endsWith('.lean')) return undefined;
  return filePath;
}

function pathIsAbsolute(value: string): boolean {
  return value.startsWith('/') || /^[A-Za-z]:\//u.test(value);
}

function readGitSource(workspace: string, commit: string, relativePath: string): string | undefined {
  if (!workspace || !commit || !relativePath) return undefined;
  try {
    return execFileSync('git', ['show', `${commit}:${relativePath}`], {
      cwd: workspace,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      maxBuffer: 512 * 1024,
    });
  } catch {
    return undefined;
  }
}

/**
 * Compare the assignment base and committed candidate at declaration level.
 * This is runtime evidence of source work, never a substitute for Lean
 * verification. Missing Git objects simply produce no source-progress claim.
 */
export function deriveMathematicsSourceProgress(
  assignment: ResearchTeamAssignment,
  git: Readonly<Record<string, unknown>> | undefined,
  preparedGit?: ProjectGitResearchTeamAssignmentReceipt['preparedGit']
): MathSourceProgress | undefined {
  if (assignment.math?.stage !== 'formalize' || assignment.laneId !== 'lean-engineering' || !git) return undefined;
  const baseCommit = preparedGit?.progressBaseCommit?.trim() || assignment.git.baseCommit;
  const candidateCommit = typeof git.headCommit === 'string' ? git.headCommit.trim() : '';
  if (!candidateCommit || candidateCommit === baseCommit) return undefined;
  const candidateWorkspace =
    preparedGit?.worktreePath && path.isAbsolute(preparedGit.worktreePath)
      ? preparedGit.worktreePath
      : typeof git.worktreePath === 'string' && path.isAbsolute(git.worktreePath)
        ? git.worktreePath
        : typeof assignment.git.worktreePath === 'string' && path.isAbsolute(assignment.git.worktreePath)
          ? assignment.git.worktreePath
          : assignment.git.projectRoot;
  const solverProjectRoot = preparedGit?.solverProjectRoot || candidateWorkspace;
  const solverPrefix = path.relative(candidateWorkspace, solverProjectRoot);
  if (solverPrefix.startsWith('..') || path.isAbsolute(solverPrefix)) return undefined;
  const candidates = assignment.math.artifactPaths?.length
    ? assignment.math.artifactPaths
    : assignment.expectedArtifacts;
  let discoveredProgress: MathSourceProgress | undefined;
  for (const artifact of candidates) {
    const relativePath = projectRelativeLeanArtifactPathForSource(artifact);
    if (!relativePath) continue;
    const repositoryRelativePath = path.join(solverPrefix, relativePath).replaceAll(path.sep, '/');
    const baseSource = readGitSource(candidateWorkspace, baseCommit, repositoryRelativePath);
    const candidateSource = readGitSource(candidateWorkspace, candidateCommit, repositoryRelativePath);
    if (baseSource === undefined || candidateSource === undefined) continue;
    if (leanSourceEscapeCount(candidateSource) > leanSourceEscapeCount(baseSource)) {
      throw new Error(
        `Mathematics source progress introduces a forbidden Lean proof escape in ${artifact}; remove sorry, admit, native_decide, or a new axiom.`
      );
    }
    const baseIdentity = normalizeLeanSourceIdentity(baseSource);
    const candidateIdentity = normalizeLeanSourceIdentity(candidateSource);
    if (baseIdentity === candidateIdentity) continue;
    const baseDeclarations = sourceDeclarationSlices(baseSource);
    const candidateDeclarations = sourceDeclarationSlices(candidateSource);
    const changedNames = new Set<string>();
    for (const [key, candidateDeclaration] of candidateDeclarations) {
      const baseDeclaration = baseDeclarations.get(key);
      if (!baseDeclaration || baseDeclaration.body !== candidateDeclaration.body) {
        changedNames.add(candidateDeclaration.name);
      }
    }
    if (!changedNames.size || discoveredProgress) continue;
    discoveredProgress = Object.freeze({
      artifactPath: artifact.trim().replaceAll('\\', '/'),
      changedDeclarationNames: Object.freeze([...changedNames].sort()),
      baseSourceHash: crypto.createHash('sha256').update(baseIdentity, 'utf8').digest('hex'),
      candidateSourceHash: crypto.createHash('sha256').update(candidateIdentity, 'utf8').digest('hex'),
    });
  }
  return discoveredProgress;
}

export const MATHEMATICS_RESEARCH_HANDOFF_ROOT = '.deepscientist/science-artifacts/math-research-handoffs' as const;

export function mathematicsAssignmentRequiresExactLeanHandoff(assignment: ResearchTeamAssignment): boolean {
  // Keep the exported predicate for callers that still import the old
  // protocol, but do not allow a Strategy assignment to opt into executable
  // Lean work. Strategy is always advisory; compiler validation belongs to a
  // Lean Engineer or the independent evaluator. In particular, this avoids a
  // legacy/partially hydrated assignment starting an unbounded handoff job.
  void assignment;
  return false;
}

/**
 * Detect an advisory task that asks the Worker to perform executable Lean
 * work. This is deliberately narrower than the legacy exact-handoff matcher:
 * mentioning an already compiled handoff is fine, while an imperative compile
 * or source-production request must be rejected before a Worker starts.
 */
export function mathematicsAdvisoryRequestsExecutableLeanWork(assignment: ResearchTeamAssignment): boolean {
  if (assignment.laneId !== 'strategy-exploration' || assignment.executionMode !== 'advisory') return false;
  const clauses = [
    assignment.title,
    assignment.objective,
    ...assignment.acceptanceCriteria,
    ...assignment.expectedArtifacts,
  ]
    .flatMap((value) => value.split(/[.!?;]+/u))
    .map((clause) => clause.trim())
    .filter(Boolean);
  return clauses.some((clause) => {
    const requestsBoundedRuntimeProbe =
      Boolean(assignment.math?.fastCheck?.runtimeProbe) &&
      /\bprobe\b/iu.test(clause) &&
      !/\b(?:produce|write|create|return|provide|develop|implement)\b[^.!?;]{0,96}\b(?:complete|full|durable)?\s*(?:lean\s+)?(?:file|proof|source|handoff|scaffold|artifact)\b/iu.test(
        clause
      );
    // A structured runtimeProbe is executed by the host in a disposable file.
    // It gives Strategy a falsification tool without granting source ownership,
    // a general compiler shell, or proof-receipt authority.
    if (requestsBoundedRuntimeProbe) return false;
    const asksForAction =
      /\b(?:must|need to|produce|write|create|compile|return|provide|develop|implement|execute|check|test|run|invoke|use)\b/iu.test(
        clause
      );
    // Mentioning a Lean-ready bridge is still valid advisory output. Require
    // an executable target such as a compiler invocation, complete source,
    // handoff, scaffold, or artifact before rejecting the assignment.
    const executableTarget =
      /\b(?:compile|compiled|compiler|lake\s+(?:env\s+)?lean|complete\s+(?:exact\s+)?lean\s+source|lean\s+(?:compiler|command|file|proof|source|handoff|scaffold|artifact)|handoff|scaffold|artifact)\b/iu.test(
        clause
      );
    if (!asksForAction || !executableTarget) return false;
    // Reading an existing, already-compiled handoff is advisory context. It
    // becomes executable work only when the same clause asks to compile or
    // invoke a checker again.
    if (
      /\b(?:already|previously|pre[- ]?)\s*compiled\b/iu.test(clause) &&
      !/\b(?:compile|run|invoke|execute|check|test)\b/iu.test(clause)
    ) {
      return false;
    }
    // A prohibition applies only when it actually scopes the executable
    // target. For example, "run lake env lean without changing files" still
    // requests a compiler invocation, while "return a bridge without
    // compiling" is a valid advisory request.
    const negatedTarget =
      /\b(?:do not|don't|never|without)\b[^.!?;]{0,96}\b(?:compile|compiled|compiler|lake\s+(?:env\s+)?lean|complete\s+(?:exact\s+)?lean\s+source|lean\s+(?:compiler|command|file|proof|source|handoff|scaffold|artifact)|handoff|scaffold|artifact)\b/iu.test(
        clause
      );
    return !negatedTarget;
  });
}

export function mathematicsExactLeanHandoffArtifactPath(assignment: ResearchTeamAssignment): string {
  const key = crypto.createHash('sha256').update(assignment.assignmentId, 'utf8').digest('hex').slice(0, 24);
  return `${MATHEMATICS_RESEARCH_HANDOFF_ROOT}/${key}.lean`;
}

export function mathematicsExactLeanHandoffCompileReceiptPath(assignment: ResearchTeamAssignment): string {
  return `${mathematicsExactLeanHandoffArtifactPath(assignment)}.compile.json`;
}

const activeMathRouteCard = (assignment: ResearchTeamAssignment): MathRouteCard | undefined => {
  const math = assignment.math;
  return math?.routeCards?.find((card) => card.routeFingerprint === math.routeFingerprint);
};

type MathematicsMethodClass =
  | 'symbolic_proof'
  | 'symbolic_consistency'
  | 'local_api'
  | 'bounded_computation'
  | 'route_strategy';

export function mathematicsAssignmentMethodClass(assignment: ResearchTeamAssignment): MathematicsMethodClass {
  const routeIdentity = [assignment.roleLabel, assignment.math?.routeFingerprint]
    .filter((value): value is string => Boolean(value))
    .join(' ')
    .toLowerCase();
  const taskText = [assignment.title, assignment.objective]
    .filter((value): value is string => Boolean(value))
    .join(' ')
    .toLowerCase()
    // Method restrictions describe what must not happen and must never select
    // that prohibited method (for example, "do not run numerical searches").
    .replace(/\b(?:do not|don't|never|avoid|without)\b[^.!?;]*(?:[.!?;]|$)/gu, ' ');
  const routeText = `${routeIdentity} ${taskText}`;

  if (/consistency|degeneracy|contradiction/u.test(routeIdentity)) return 'symbolic_consistency';
  if (
    /bounded[-_ ][a-z0-9_-]{0,32}(?:computation|experiment|search|sweep|probe)|(?:numerical|finite|random)[-_ ]?(?:search|sweep|experiment|probe)|counterexample[-_ ]?(?:search|probe)|coordinate[-_ ]?fitting/u.test(
      routeIdentity
    )
  ) {
    return 'bounded_computation';
  }
  if (
    /local[-_ ]?api|mathlib[-_ ]?(?:api|lookup|retrieval)|(?:api|premise|declaration|theorem)[-_ ]?(?:helper|lookup|retrieval)/u.test(
      routeIdentity
    )
  ) {
    return 'local_api';
  }
  if (
    /synthetic|pure geometry|natural.language|proof development|coordinate|vector|algebra|trigon|induction|combinator|inner.product|angle.chase/u.test(
      routeIdentity
    )
  ) {
    return 'symbolic_proof';
  }

  if (/consistency|degeneracy|contradiction/u.test(taskText)) return 'symbolic_consistency';
  if (
    /(?:run|perform|conduct|execute|use)\b[^.!?;]{0,80}\b(?:computation|numerical experiment|numerical search|finite search|counterexample search)/u.test(
      taskText
    )
  ) {
    return 'bounded_computation';
  }
  if (
    /(?:inspect|query|locate|retrieve|look up|search)\b[^.!?;]{0,80}\b(?:mathlib|library|api|declaration|premise)/u.test(
      taskText
    )
  ) {
    return 'local_api';
  }
  if (
    /synthetic|pure geometry|natural.language|proof development|coordinate|vector|algebra|trigon|induction|combinator/u.test(
      routeText
    )
  ) {
    return 'symbolic_proof';
  }
  return 'route_strategy';
}

/** Runtime-owned method boundary for a blind advisory route. */
function createMathematicsMethodContract(
  assignment: ResearchTeamAssignment,
  target: ResearchTeamRosterMember
): Readonly<Record<string, unknown>> | undefined {
  if (target.laneId !== 'strategy-exploration' || !assignment.math) return undefined;
  const proposesCandidate = assignment.math.routeProposalMode === 'candidate';
  const methodClass = mathematicsAssignmentMethodClass(assignment);
  const problemId = assignment.math.problemContract?.problemId ?? assignment.math.researchContract?.problemId ?? '';
  const blindRun = /^imo(?:\d+)?[_-]/iu.test(problemId) || /^imo\d/iu.test(problemId);
  const requiredOutcome = proposesCandidate
    ? 'Return exactly one surviving mathRouteCard for this candidate route, retaining the decisive symbolic bridge and probe evidence on a non-proposed plan node.'
    : methodClass === 'local_api'
      ? 'Return the exact declaration and type needed by this route, or a precise missing API bridge with the next constructive dependency.'
      : methodClass === 'bounded_computation'
        ? 'Turn the bounded experiment into one symbolic conjecture, counterexample, or exact obstruction before delivery.'
        : methodClass === 'symbolic_consistency'
          ? 'Return a symbolic consequence, contradiction, or exact obstruction derived from the stated hypotheses.'
          : 'Return one decisive symbolic bridge, falsification, or exact obstruction for this route.';
  const methodProhibitions =
    methodClass === 'bounded_computation'
      ? [
          'Do not expand or repeat numerical sweeps after the experiment has identified its symbolic claim.',
          'Do not present numerical residuals as proof evidence.',
        ]
      : methodClass === 'local_api'
        ? [
            'Do not run numerical solvers or use numerical examples as route discovery.',
            'Do not widen local source inspection beyond declarations needed by the assigned bridge.',
          ]
        : [
            'Do not run numerical solvers, random searches, or coordinate fitting.',
            'Do not switch to another route or duplicate a computation lane.',
          ];
  const advisoryBoundary = proposesCandidate
    ? 'This is an advisory route-candidate episode. Return mathRouteCard, never mathResearchFinding. Use only plan-node roles goal|reduction|auxiliary|case_split|bridge and statuses proposed|sourced|counterexample_checked; do not write or compile a complete Lean handoff, claim kernel verification, or provide runtime-owned identity fields.'
    : 'This is an advisory research episode. You may run only an assignment-bound bounded counterexample probe in a host-owned disposable Lean file. Do not write or compile a complete Lean handoff, invoke a handoff checker, modify canonical source, or claim a durable compiler receipt; return the decisive mathematical bridge, obstruction, or falsification as mathResearchFinding and leave proof validation to the Lean Engineer.';
  const convergenceProtocol = proposesCandidate
    ? Object.freeze({
        trigger:
          'Once one decisive probe either supports or eliminates the candidate route, the route-card outcome is satisfied even when the original theorem remains open.',
        nextToolCall: 'research_team(action="deliver") must be the next tool call in this turn.',
        delivery:
          'Deliver one mathRouteCard with the retained evidence, the first unresolved obligation, and one nextSingleObjective; a blocked route card is useful research progress.',
        missingLibrary:
          'A missing theorem is route evidence for the Lead, not a reason to keep searching in this Worker turn. The Lead may route helper construction to the Lean Engineer.',
      })
    : Object.freeze({
        trigger:
          'Once a targeted retrieval and one discriminating probe establish an exact declaration, symbolic bridge, falsification, or missing dependency, the advisory outcome is satisfied.',
        nextToolCall: 'research_team(action="deliver") must be the next tool call in this turn.',
        delivery:
          'Deliver one mathResearchFinding with the exact evidence reference, the first unresolved bottleneck, and one nextAction; delivery reports research progress and does not terminate the original theorem.',
        missingLibrary:
          'A missing Mathlib theorem or high-level API is a precise route obstruction to hand to the Lead. Do not treat it as proof of impossibility and do not search beyond the targeted evidence needed to name the next helper dependency.',
      });
  return Object.freeze({
    runtimeOwned: true,
    methodClass,
    routeBoundary: assignment.math.routeFingerprint,
    ...(blindRun ? { externalNetwork: 'forbidden', protectedSolutions: 'forbidden' } : {}),
    requiredOutcome,
    convergenceProtocol,
    prohibitedActions: Object.freeze([
      ...(blindRun
        ? ['Do not use Web search, browsers, remote sources, prior solutions, or protected evaluator material.']
        : []),
      ...methodProhibitions,
      ...(proposesCandidate
        ? [
            'Do not return mathResearchFinding for this assignment; the result must contain one mathRouteCard.',
            'Every plan node must use role goal|reduction|auxiliary|case_split|bridge and kind theorem|definition|api_bridge|ported_helper.',
            'Use status proposed for unverified nodes; use sourced or counterexample_checked only when evidenceRefs contains the exact supporting probe reference.',
            'Include exactly one goal node matching rootNodeId, use dependsOn for graph edges, and keep the candidate to the shortest useful linear plan unless independent lemmas require branching.',
            'Do not write or compile a complete Lean handoff during this advisory route episode.',
          ]
        : []),
      advisoryBoundary,
    ]),
    stopRule: proposesCandidate
      ? 'Deliver immediately after one decisive probe has either supported or eliminated the candidate route; do not emit a generic finding or continue polishing the route card. The next tool call after that probe must be research_team(action="deliver").'
      : 'Deliver immediately once the required symbolic bridge, exact obstruction, or falsification is actionable; do not keep polishing, compile a handoff, or broaden the assignment. The next tool call after that evidence must be research_team(action="deliver").',
  });
}

/** Keep absent library infrastructure inside the proof frontier, not the runtime-failure lane. */
function createMathematicsFormalizationPolicy(
  assignment: ResearchTeamAssignment,
  target: ResearchTeamRosterMember
): Readonly<Record<string, unknown>> | undefined {
  if (target.laneId !== 'lean-engineering' || !assignment.math) return undefined;
  const officialManifestId = assignment.math.problemContract?.officialManifestId ?? '';
  const isLeanEval = officialManifestId.startsWith('lean-eval:');
  const activeRoute = activeMathRouteCard(assignment);
  const activeNode = activeRoute?.planNodes.find((node) => node.id === assignment.math?.activePlanNodeId);
  const firstCompileObjective =
    activeNode?.provisionalLeanStatement ?? assignment.math.researchContract?.nextAction ?? assignment.objective;
  const executionPolicy = assignment.math.executionPolicy;
  return Object.freeze({
    runtimeOwned: true,
    benchmark: isLeanEval ? 'lean-eval' : 'generic-lean',
    gapDisposition: 'dependency_milestone',
    nonTerminalGaps: Object.freeze([
      'A missing theorem, API, construction, helper, or larger dependency graph remains proof work.',
    ]),
    episodeLoop: Object.freeze([
      'Inspect the local goal and map its smallest missing dependency.',
      'Query local premises; use approved public sources only when needed.',
      'Implement in authorized files and compile the changed boundary.',
      'Retain the best compiling state and continue from the next dependency.',
    ]),
    firstCompileObjective,
    ...(executionPolicy
      ? {
          policyRule:
            'Use math.executionPolicy at its current cursor. Advance after failure and do not repeat an attempted item on an unchanged proof state.',
        }
      : {}),
    firstCompileRule:
      'Compile the smallest helper or declaration cluster that establishes this objective before extending the whole theorem body. Do not restart route discovery inside the formalizer.',
    semanticViabilityGate: 'Do not claim completion unless the complete original target closes.',
    validStopConditions: Object.freeze([
      'the assigned goal is closed',
      'a placeholder-free compiled helper or strictly smaller Lean goal is retained',
      'the exact route is formally refuted or structurally invalid',
      'Lean or a required execution service cannot run, or the authorized proof files cannot be written',
    ]),
    stopRule:
      'Continue while Lean runs, the proof files are writable, and a dependency milestone remains. A catalog of absent library APIs is not a result or an infrastructure blocker.',
    upstreamPremiseRetrieval: Object.freeze({
      tool: 'math_portfolio',
      activation: 'Only after local import-closure retrieval misses on a live Lean goal.',
      proofBodyPolicy: 'Discard remote proof bodies; retain declaration metadata only.',
      validation: 'Verify every hit with the pinned imports and target build.',
    }),
    ...(isLeanEval
      ? {
          solverWriteScope: Object.freeze(['Submission.lean', 'Submission/**/*.lean']),
          protectedInputs: Object.freeze([
            'Never read, search, quote, copy, or import Solution.lean.',
            'Keep Challenge.lean, config.json, holes.json, lakefile.toml, lean-toolchain, and WorkspaceTest.lean read-only.',
          ]),
          constructionCheck:
            'Run a targeted lake build for each changed Submission module and reject sorry, admit, native_decide, unsafe, or new axioms in retained helpers.',
          officialCheck:
            'Do not run lake test or the official comparator during construction; the Lead owns the final unchanged-revision check.',
          remoteScope:
            'Public papers, cited literature, Mathlib, Reservoir, and unrelated Lean packages are allowed with provenance. Reference solutions, prior submissions, competition PRs, answer repositories, and evaluator material remain forbidden.',
        }
      : {}),
  });
}

/** Keep only actionable first-episode rules on the LeanEval Worker wire. */
function projectLeanEvalFormalizationPolicy(
  policy: Readonly<Record<string, unknown>>
): Readonly<Record<string, unknown>> {
  return Object.freeze({
    runtimeOwned: true,
    benchmark: policy.benchmark,
    gapDisposition: policy.gapDisposition,
    objective: policy.firstCompileObjective,
    actionRule:
      'Do not assess whole-theorem difficulty after lookup or run another search. Immediately edit the assigned local dependency, build it, and repair from Lean output.',
    stopRule: policy.stopRule,
    ...(policy.solverWriteScope ? { solverWriteScope: policy.solverWriteScope } : {}),
    ...(policy.protectedInputs ? { protectedInputs: policy.protectedInputs } : {}),
    ...(policy.constructionCheck ? { constructionCheck: policy.constructionCheck } : {}),
  });
}

// Context is bounded by bytes, not arbitrary record counts.  This preserves
// every relevant short entry while still preventing an unbounded history from
// blowing up a Worker prompt.
const MAX_PROJECTED_CONTEXT_BYTES = 24 * 1024;

function fitsProjectedBudget(value: unknown, usedBytes: number, budget = MAX_PROJECTED_CONTEXT_BYTES): boolean {
  return usedBytes + Buffer.byteLength(JSON.stringify(value), 'utf8') <= budget;
}

export type MathematicsAssignmentProjectionEfficiency = Readonly<{
  assignment_payload_bytes: number;
  full_assignment_bytes: number;
  projection_ratio: number;
  route_cards_injected: number;
  proof_pack_nodes_injected: number;
  lessons_injected: number;
  premises_injected: number;
}>;

export type MathematicsAssignmentProjection = Readonly<{
  assignment: Readonly<Record<string, unknown>>;
  serializedAssignment: string;
  efficiency: MathematicsAssignmentProjectionEfficiency;
}>;

type MathematicsWorkerContextRecovery = Readonly<{
  schema: 'deepscientist.mathematics.worker-context-recovery.v1';
  source: 'math_research';
  action: 'get';
  request: Readonly<{
    problemId: string;
    assignmentId: string;
    command: Readonly<{ action: 'get'; limit: number }>;
  }>;
  statementHash: string;
  routeFingerprint: string;
  activePlanNodeId?: string;
  durableResearchContractDigest: string;
  omittedCounts: Readonly<Record<string, number>>;
  omittedDigests: Readonly<Record<string, string>>;
  instruction: string;
}>;

export type MathematicsProofFrontierPacket = Readonly<{
  schema: 'deepscientist.mathematics.proof-frontier-packet.v1';
  packetHash: string;
  statementHash: string;
  routeFingerprint: string;
  activePlanNodeId?: string;
  currentGoal?: string;
  localContextHash?: string;
  verifiedFacts: readonly string[];
  lastTwoDiagnostics: readonly string[];
  failedActions: readonly string[];
  nextAcceptanceCriteria: readonly string[];
  availableSupportReceipts: readonly string[];
}>;

/**
 * Small, stable control surface for a Worker turn.  The durable assignment
 * remains lossless, while this packet tells the model what the next turn must
 * change and which evidence can close it.  Keeping this separate from the
 * projected history prevents context compaction from removing the action
 * contract together with old notes.
 */
export type MathematicsWorkerActionContract = Readonly<{
  schema: 'deepscientist.mathematics.worker-action-contract.v1';
  activeObligation: string;
  nextAction: string;
  requiredEvidence: readonly string[];
  failureTransition: string;
}>;

function compactMathematicsFrontierText(value: string, limit: number): string {
  const normalized = value.trim();
  return normalized.length <= limit
    ? normalized
    : `${normalized.slice(0, Math.max(0, limit - 32))}\n...[frontier context compacted]`;
}

const MATHEMATICS_FAILURE_RECOVERY_HINTS: Partial<Record<MathFailureCategory, string>> = {
  lean_error: 'Repair the first concrete Lean diagnostic before attempting a broader proof change.',
  missing_hole: 'Expose the missing term type and construct that dependency before extending the parent proof.',
  import_or_olean_mismatch:
    'Verify the exact import, namespace and pinned declaration before changing the theorem statement.',
  actual_proof_failure:
    'Change the failing inference, premise or representation while preserving checked dependencies.',
  duplicate_route: 'Select a structurally distinct route; repeating the same proof frontier is not progress.',
  wrong_statement: 'Reconcile the live goal with the original statement and do not add an unsupported premise.',
  counterexample: 'Check whether the counterexample targets a surrogate claim or the exact original hypotheses.',
  review_gap: 'Address the review finding with a new kernel or goal-state check before resubmitting.',
};

function buildMathematicsWorkerActionContract(
  input: Readonly<{
    assignment: ResearchTeamAssignment;
    activeNode?: MathPlanNode;
  }>
): MathematicsWorkerActionContract {
  const compact = (value: string, limit = 2_048): string => {
    const normalized = value.trim();
    return normalized.length <= limit
      ? normalized
      : `${normalized.slice(0, limit - 32)}\n...[action context compacted]`;
  };
  const math = input.assignment.math;
  const activeObligation =
    input.activeNode?.provisionalLeanStatement?.trim() ||
    math?.researchContract?.activeBottleneck?.trim() ||
    math?.researchContract?.nextAction?.trim() ||
    input.assignment.objective.trim();
  const advisoryStrategy =
    input.assignment.laneId === 'strategy-exploration' && input.assignment.executionMode === 'advisory';
  const nextAction = advisoryStrategy
    ? 'After the first targeted retrieval and discriminating probe, call research_team(action="deliver") immediately with the best evidence.'
    : math?.researchContract?.nextAction?.trim() ||
      input.activeNode?.successCriteria?.[0]?.trim() ||
      input.assignment.objective.trim();
  const requiredEvidence = Object.freeze(
    [...(input.activeNode?.successCriteria ?? []), ...(math?.researchContract?.openObligations ?? []).slice(0, 3)]
      .map((value) => compact(value, 1_024))
      .filter(Boolean)
      .slice(0, 6)
  );
  const failureLedger = math?.failureLedger;
  const failureDetails = [
    failureLedger?.firstLeanError ? `First Lean diagnostic: ${compact(failureLedger.firstLeanError, 520)}` : undefined,
    failureLedger?.latestReceipt ? `Latest proof receipt: ${compact(failureLedger.latestReceipt, 520)}` : undefined,
  ].filter((value): value is string => Boolean(value));
  const failureHint = failureLedger?.failureCategory
    ? MATHEMATICS_FAILURE_RECOVERY_HINTS[failureLedger.failureCategory]
    : undefined;
  const lastFailedAction = math?.proofState?.actionHistory
    ?.toReversed()
    .find((action) => action.outcome === 'failed')?.payload;
  const actionMemory = lastFailedAction ? `Last failed action: ${compact(lastFailedAction, 520)}` : undefined;
  const failureTransition =
    failureDetails.length || failureHint || actionMemory
      ? compact(
          [
            'Use the latest diagnostic to choose a new tactic, premise, or route transition; do not repeat the same proof state.',
            failureHint,
            actionMemory,
            ...failureDetails,
          ]
            .filter(Boolean)
            .join(' ')
        )
      : advisoryStrategy
        ? 'If the exact bridge or missing dependency is now identifiable, call research_team(action="deliver") next; delivery is progress and does not end the original theorem.'
        : math?.stage === 'formalize'
          ? 'Compile the smallest dependency-ready declaration, retain its receipt, and continue from the resulting live goal.'
          : 'Return one actionable mathematical bridge, obstruction, or falsification tied to the original target.';
  return Object.freeze({
    schema: 'deepscientist.mathematics.worker-action-contract.v1',
    activeObligation: compact(activeObligation),
    nextAction: compact(nextAction),
    requiredEvidence,
    failureTransition,
  });
}

export function buildMathematicsProofFrontierPacket(
  input: Readonly<{
    statementHash: string;
    routeFingerprint: string;
    activePlanNode?: MathPlanNode;
    proofState?: Pick<MathProofState, 'openGoals' | 'localContextHash' | 'actionHistory'>;
    failureLedger?: MathFailureLedger;
    supportReceipts?: readonly string[];
  }>
): MathematicsProofFrontierPacket {
  const bounded = (value: string | undefined, limit: number): string | undefined =>
    value === undefined ? undefined : compactMathematicsFrontierText(value, limit);
  const verifiedFacts = Object.freeze([...(input.failureLedger?.verifiedPlanNodeIds ?? [])].slice(-8));
  const lastTwoDiagnostics = Object.freeze(
    [input.failureLedger?.firstLeanError, input.failureLedger?.latestReceipt]
      .filter((value): value is string => Boolean(value?.trim()))
      .map((value) => compactMathematicsFrontierText(value, 2_048))
      .slice(-2)
  );
  const failedActions = Object.freeze(
    (input.proofState?.actionHistory ?? [])
      .filter((action) => action.outcome === 'failed')
      .slice(-4)
      .map((action) => action.payload)
      .filter((value): value is string => Boolean(value?.trim()))
      .map((value) => compactMathematicsFrontierText(value, 1_024))
  );
  const payload = {
    schema: 'deepscientist.mathematics.proof-frontier-packet.v1' as const,
    statementHash: input.statementHash,
    routeFingerprint: input.routeFingerprint,
    ...(input.activePlanNode?.id ? { activePlanNodeId: input.activePlanNode.id } : {}),
    ...(bounded(input.proofState?.openGoals?.[0], 4_096)
      ? { currentGoal: bounded(input.proofState?.openGoals?.[0], 4_096) }
      : {}),
    ...(input.proofState?.localContextHash ? { localContextHash: input.proofState.localContextHash } : {}),
    verifiedFacts,
    lastTwoDiagnostics,
    failedActions,
    nextAcceptanceCriteria: Object.freeze(
      [...(input.activePlanNode?.successCriteria ?? [])]
        .slice(0, 4)
        .map((value) => compactMathematicsFrontierText(value, 1_024))
    ),
    availableSupportReceipts: Object.freeze(
      [...(input.supportReceipts ?? [])].slice(-8).map((value) => compactMathematicsFrontierText(value, 512))
    ),
  };
  const packetHash = crypto.createHash('sha256').update(JSON.stringify(payload), 'utf8').digest('hex');
  return Object.freeze({ ...payload, packetHash });
}

function refreshMathematicsProofFrontierPacketHash(packet: Record<string, unknown>): void {
  const { packetHash: _packetHash, ...payload } = packet;
  packet.packetHash = crypto.createHash('sha256').update(JSON.stringify(payload), 'utf8').digest('hex');
}

/**
 * Keep the durable assignment complete, but send each Mathematics Worker only
 * the context its lane can act on.
 */
export function projectMathematicsAssignmentForWorker(
  assignment: ResearchTeamAssignment,
  target: ResearchTeamRosterMember,
  portfolio?: MathematicsPortfolio
): MathematicsAssignmentProjection {
  const serializedFullAssignment = JSON.stringify(assignment);
  const fullAssignmentBytes = Buffer.byteLength(serializedFullAssignment, 'utf8');
  if (!assignment.math) {
    return Object.freeze({
      assignment,
      serializedAssignment: serializedFullAssignment,
      efficiency: assignmentProjectionEfficiency(assignment, fullAssignmentBytes, fullAssignmentBytes),
    });
  }

  const lessons =
    target.laneId === 'independent-review'
      ? Object.freeze([])
      : selectApplicableLessons(
          assignment.math.applicableLessons ?? [],
          assignment.math.routeFingerprint,
          assignment.math.routePattern
        );
  const commonMath = {
    stage: assignment.math.stage,
    workflowStage: assignment.math.workflowStage,
    statementHash: assignment.math.statementHash,
    routeFingerprint: assignment.math.routeFingerprint,
    ...(assignment.math.executionPolicy ? { executionPolicy: assignment.math.executionPolicy } : {}),
    ...(assignment.math.directAttempt ? { directAttempt: true } : {}),
    ...(assignment.math.sessionContinuation ? { sessionContinuation: assignment.math.sessionContinuation } : {}),
    fastCheck: assignment.math.fastCheck,
    ...(assignment.math.artifactPaths ? { artifactPaths: assignment.math.artifactPaths } : {}),
    ...(assignment.math.problemContract ? { problemContract: assignment.math.problemContract } : {}),
    ...(assignment.math.researchContract
      ? { researchContract: projectResearchContract(assignment.math.researchContract) }
      : {}),
    ...(assignment.math.alignmentCheck ? { alignmentCheck: assignment.math.alignmentCheck } : {}),
  };
  const problemId = assignment.math.problemContract?.problemId ?? assignment.math.researchContract?.problemId;
  const activeRoute = activeMathRouteCard(assignment);
  const activeNode = activeRoute?.planNodes.find((node) => node.id === assignment.math?.activePlanNodeId);
  const actionContract = buildMathematicsWorkerActionContract({ assignment, activeNode });
  const mechanismCapsules =
    target.laneId === 'strategy-exploration' && portfolio && problemId
      ? deriveMathematicsMechanismCapsules(portfolio, {
          problemId,
          routeFingerprint: assignment.math.routeFingerprint,
          query: [
            assignment.objective,
            assignment.math.researchContract?.objective ?? '',
            assignment.math.researchContract?.context ?? '',
            assignment.math.researchContract?.activeBottleneck ?? '',
            assignment.math.routePattern ?? '',
          ],
          limit: 3,
        })
      : Object.freeze([]);
  let projectedMath: Readonly<Record<string, unknown>>;

  if (target.laneId === 'lean-engineering') {
    const helperFirst = activeNode?.kind === 'api_bridge' || activeNode?.kind === 'ported_helper';
    const frontierPacket = buildMathematicsProofFrontierPacket({
      statementHash: assignment.math.statementHash,
      routeFingerprint: assignment.math.routeFingerprint,
      activePlanNode: activeNode,
      proofState: assignment.math.proofState,
      failureLedger: assignment.math.failureLedger,
      supportReceipts: activeNode?.evidenceRefs,
    });
    projectedMath = Object.freeze({
      ...commonMath,
      ...(assignment.math.routePattern ? { routePattern: assignment.math.routePattern } : {}),
      ...(assignment.math.previousConsecutiveStalls !== undefined
        ? { previousConsecutiveStalls: assignment.math.previousConsecutiveStalls }
        : {}),
      ...(assignment.math.activePlanNodeId ? { activePlanNodeId: assignment.math.activePlanNodeId } : {}),
      ...(assignment.math.routeSelection ? { routeSelection: assignment.math.routeSelection } : {}),
      ...(assignment.math.routeProbeReceipt ? { routeProbeReceipt: assignment.math.routeProbeReceipt } : {}),
      ...(assignment.math.proofState ? { proofState: assignment.math.proofState } : {}),
      frontierPacket,
      ...(activeRoute && assignment.math.activePlanNodeId
        ? {
            routePhase: 'active_node',
            ...(helperFirst
              ? {
                  helperFirst: true,
                  proofStrategy: 'helper_first',
                  helperObjective:
                    'Compile and kernel-verify the dependency-ready helper before extending the parent theorem.',
                }
              : {}),
            proofPack: createActiveNodeProofPack(
              activeRoute,
              assignment.math.activePlanNodeId,
              assignment.math.failureLedger,
              assignment.math.researchContract?.solutionSketchRef,
              assignment.math.problemContract?.problemId ?? assignment.math.researchContract?.problemId
            ),
          }
        : {}),
      ...(lessons.length ? { applicableLessons: lessons } : {}),
      ...(assignment.math.failureLedger ? { failureLedger: projectFailureLedger(assignment.math.failureLedger) } : {}),
      actionContract,
    });
  } else if (target.laneId === 'independent-review') {
    projectedMath = Object.freeze({
      ...commonMath,
      ...(assignment.math.routeSelection ? { routeSelection: assignment.math.routeSelection } : {}),
      ...(assignment.math.localGateReceipt ? { localGateReceipt: assignment.math.localGateReceipt } : {}),
      actionContract,
    });
  } else {
    projectedMath = Object.freeze({
      ...commonMath,
      routePhase: assignment.math.routeProposalMode ?? 'research',
      ...(assignment.math.routeProposalMode ? { routeProposalMode: assignment.math.routeProposalMode } : {}),
      ...(assignment.math.routePattern ? { routePattern: assignment.math.routePattern } : {}),
      ...(assignment.math.previousConsecutiveStalls !== undefined
        ? { previousConsecutiveStalls: assignment.math.previousConsecutiveStalls }
        : {}),
      ...(lessons.length ? { applicableLessons: lessons } : {}),
      ...(assignment.math.failureLedger ? { failureLedger: projectFailureLedger(assignment.math.failureLedger) } : {}),
      ...(mechanismCapsules.length ? { mechanismCapsules } : {}),
      actionContract,
    });
  }

  const methodContract = createMathematicsMethodContract(assignment, target);
  const formalizationPolicy = createMathematicsFormalizationPolicy(assignment, target);
  const directFormalizeFailureCriteria =
    target.laneId === 'lean-engineering' &&
    assignment.math.stage === 'formalize' &&
    assignment.math.directAttempt === true
      ? Object.freeze([
          'The exact route is formally refuted or structurally invalid, with the decisive evidence retained.',
          'Lean or a required execution service cannot run, or the authorized proof files cannot be written.',
        ])
      : undefined;
  const resultContractVariant =
    target.laneId === 'lean-engineering' && assignment.math.directAttempt === true
      ? 'direct-formalization'
      : target.laneId === 'strategy-exploration' && assignment.math.routeProposalMode !== 'candidate'
        ? 'research-finding'
        : 'complete';
  const reuseSourceSlot = assignment.math.sessionContinuation?.mode === 'reuse_source_slot';
  const compactLeanEvalDirectAttempt =
    !reuseSourceSlot &&
    target.laneId === 'lean-engineering' &&
    assignment.math.directAttempt === true &&
    formalizationPolicy?.benchmark === 'lean-eval';
  const formalizationPolicyForWorker = formalizationPolicy
    ? compactLeanEvalDirectAttempt
      ? projectLeanEvalFormalizationPolicy(formalizationPolicy)
      : formalizationPolicy
    : undefined;
  const workerAssignment = reuseSourceSlot
    ? Object.freeze({
        schema: assignment.schema,
        assignmentId: assignment.assignmentId,
        workflowId: assignment.workflowId,
        laneId: assignment.laneId,
        ...(assignment.roleTemplateId ? { roleTemplateId: assignment.roleTemplateId } : {}),
        ...(assignment.roleKind ? { roleKind: assignment.roleKind } : {}),
        ...(assignment.roleLabel ? { roleLabel: assignment.roleLabel } : {}),
        ...(assignment.roleInstructions ? { roleInstructions: assignment.roleInstructions } : {}),
        ...(assignment.executionMode ? { executionMode: assignment.executionMode } : {}),
        title: assignment.title,
        objective: assignment.objective,
        acceptanceCriteria: assignment.acceptanceCriteria,
        failureCriteria: assignment.failureCriteria,
        // The source conversation already owns the immutable statement and
        // full history.  Retain only the newest external evidence and repair
        // constraints that may have arrived since that turn.
        evidenceRefs: Object.freeze(assignment.evidenceRefs.slice(-4)),
        doNotRepeat: Object.freeze(assignment.doNotRepeat.slice(-4)),
        expectedArtifacts: assignment.expectedArtifacts,
        falsificationPlan: assignment.falsificationPlan,
        git: assignment.git,
      })
    : compactLeanEvalDirectAttempt
      ? Object.freeze({
          schema: assignment.schema,
          assignmentId: assignment.assignmentId,
          objective: assignment.objective,
          git: Object.freeze({
            baseCommit: assignment.git.baseCommit,
            ...(assignment.git.worktreePath ? { worktreePath: assignment.git.worktreePath } : {}),
          }),
        })
      : assignment;
  const workerMath = reuseSourceSlot
    ? (() => {
        const {
          fastCheck: _fastCheck,
          problemContract: _problemContract,
          researchContract: _researchContract,
          alignmentCheck: _alignmentCheck,
          applicableLessons: _applicableLessons,
          mechanismCapsules: _mechanismCapsules,
          ...continuationDelta
        } = projectedMath;
        return Object.freeze(continuationDelta);
      })()
    : compactLeanEvalDirectAttempt
      ? Object.freeze({
          stage: projectedMath.stage,
          statementHash: projectedMath.statementHash,
          routeFingerprint: projectedMath.routeFingerprint,
          directAttempt: true,
          ...(projectedMath.activePlanNodeId ? { activePlanNodeId: projectedMath.activePlanNodeId } : {}),
          problemId: assignment.math.problemContract?.problemId,
        })
      : projectedMath;
  const projected = Object.freeze({
    ...workerAssignment,
    ...(!compactLeanEvalDirectAttempt && directFormalizeFailureCriteria
      ? { failureCriteria: directFormalizeFailureCriteria }
      : {}),
    resultContract: createMathematicsWorkerResultContract(target.laneId ?? '', resultContractVariant),
    ...(methodContract ? { methodContract } : {}),
    ...(formalizationPolicyForWorker ? { formalizationPolicy: formalizationPolicyForWorker } : {}),
    ...(!compactLeanEvalDirectAttempt
      ? {
          doNotRepeat:
            target.laneId === 'independent-review'
              ? Object.freeze([])
              : projectDoNotRepeat(
                  reuseSourceSlot ? assignment.doNotRepeat.slice(-4) : assignment.doNotRepeat,
                  lessons
                ),
        }
      : {}),
    math: workerMath,
  });
  const serializedProjected = JSON.stringify(projected);
  const compacted = compactProjectedAssignment(
    projected,
    Buffer.byteLength(serializedProjected, 'utf8'),
    assignment.math.researchContract
  );
  const serializedAssignment = compacted === projected ? serializedProjected : JSON.stringify(compacted);
  const assignmentPayloadBytes = Buffer.byteLength(serializedAssignment, 'utf8');
  return Object.freeze({
    assignment: compacted,
    serializedAssignment,
    efficiency: assignmentProjectionEfficiency(projected, assignmentPayloadBytes, fullAssignmentBytes),
  });
}

/**
 * The per-field selectors above protect individual archives.  A route can
 * still contain several archives at once, though, so enforce the actual wire
 * budget on the final serialized assignment as well.  Required identity and
 * the active proof node stay intact; optional history is trimmed from oldest
 * entries first so the Worker keeps the current bottleneck and latest repair.
 */
function compactProjectedAssignment(
  projected: Readonly<Record<string, unknown>>,
  projectedBytes: number,
  durableResearchContractInput?: NonNullable<ResearchTeamAssignment['math']>['researchContract']
): Readonly<Record<string, unknown>> {
  if (projectedBytes <= MAX_PROJECTED_CONTEXT_BYTES) return projected;
  // JSON is the wire representation and gives us a detached, plain object to
  // compact.  This prevents emergency trimming from ever mutating the
  // durable assignment or a caller-owned extension object.
  const candidate: Record<string, unknown> = JSON.parse(JSON.stringify(projected)) as Record<string, unknown>;
  const math = isRecord(candidate.math) ? { ...candidate.math } : undefined;
  if (math) candidate.math = math;
  const failureLedger = math && isRecord(math.failureLedger) ? { ...math.failureLedger } : undefined;
  if (failureLedger && math) math.failureLedger = failureLedger;
  const researchContract = math && isRecord(math.researchContract) ? { ...math.researchContract } : undefined;
  if (researchContract && math) math.researchContract = researchContract;
  const durableResearchContract = durableResearchContractInput
    ? { ...durableResearchContractInput }
    : researchContract
      ? { ...researchContract }
      : undefined;
  const omittedResearchCounts: Record<string, number> = {};
  const omittedResearchDigests: Record<string, string> = {};
  const noteResearchOmission = (key: string, values: unknown): void => {
    const count = Array.isArray(values) ? values.length : values === undefined ? 0 : 1;
    if (count <= 0) return;
    omittedResearchCounts[key] = Math.max(omittedResearchCounts[key] ?? 0, count);
    omittedResearchDigests[key] = mathDigest(canonicalMathJson(values));
  };
  const proofPack = math && isRecord(math.proofPack) ? { ...math.proofPack } : undefined;
  if (proofPack && math) math.proofPack = proofPack;
  const proofState = math && isRecord(math.proofState) ? { ...math.proofState } : undefined;
  if (proofState && math) math.proofState = proofState;

  const serializedBytes = (): number => Buffer.byteLength(JSON.stringify(candidate), 'utf8');

  const trimArray = (container: Record<string, unknown> | undefined, key: string, minimum: number): void => {
    if (!container || !Array.isArray(container[key])) return;
    // Always detach the array before trimming.  A projection can be built from
    // an unfrozen test/extension object, and mutating it here would otherwise
    // corrupt the durable assignment that is meant to remain complete.
    const values = (container[key] as unknown[]).slice();
    if (serializedBytes() <= MAX_PROJECTED_CONTEXT_BYTES || values.length <= minimum) {
      container[key] = values;
      return;
    }
    // Keep the newest entries. Most math archives are append-only and the
    // newest failure/lesson is the one that changes the next action. Find the
    // largest suffix that fits with O(log n) whole-object serializations;
    // repeatedly removing prefixes made oversized assignments quadratic.
    let low = minimum;
    let high = values.length;
    let best = minimum;
    while (low <= high) {
      const keep = Math.floor((low + high) / 2);
      container[key] = values.slice(values.length - keep);
      if (serializedBytes() <= MAX_PROJECTED_CONTEXT_BYTES) {
        best = keep;
        low = keep + 1;
      } else {
        high = keep - 1;
      }
    }
    container[key] = values.slice(values.length - best);
    if (container === researchContract && best < values.length) {
      noteResearchOmission(key, values.slice(0, values.length - best));
    }
  };

  trimArray(candidate, 'doNotRepeat', 1);
  trimArray(candidate, 'acceptanceCriteria', 1);
  trimArray(candidate, 'failureCriteria', 1);
  trimArray(candidate, 'evidenceRefs', 0);
  trimArray(candidate, 'expectedArtifacts', 1);
  trimArray(math, 'applicableLessons', 1);
  trimArray(failureLedger, 'triedRoutes', 1);
  trimArray(failureLedger, 'doNotRepeatRefs', 1);
  trimArray(researchContract, 'knownResults', 1);
  trimArray(researchContract, 'establishedClaims', 1);
  trimArray(researchContract, 'conjectures', 1);
  trimArray(researchContract, 'failedApproaches', 1);
  trimArray(researchContract, 'openObligations', 1);
  trimArray(researchContract, 'insights', 1);
  trimArray(math, 'mechanismCapsules', 0);
  trimArray(proofPack, 'premiseHints', 0);
  trimArray(proofPack, 'premiseCoverage', 1);
  trimArray(proofPack, 'bridges', 0);
  trimArray(proofPack, 'premises', 1);
  trimArray(proofPack, 'dependencyNodes', 0);
  trimArray(proofState, 'actionHistory', 0);

  // A single unusually verbose sketch must not defeat the aggregate budget.
  // The live-goal premise retrieval contract remains available when a sketch
  // is shortened, so the Worker can recover missing library context cheaply.
  const trimText = (container: Record<string, unknown> | undefined, key: string, limit: number): void => {
    if (!container || typeof container[key] !== 'string' || serializedBytes() <= MAX_PROJECTED_CONTEXT_BYTES) return;
    const value = container[key] as string;
    if (value.length <= limit) return;
    container[key] = `${value.slice(0, Math.max(0, limit - 32))}\n...[context compacted]`;
  };
  const falsificationPlan = isRecord(candidate.falsificationPlan) ? { ...candidate.falsificationPlan } : undefined;
  if (falsificationPlan) candidate.falsificationPlan = falsificationPlan;
  const problemContract = math && isRecord(math.problemContract) ? { ...math.problemContract } : undefined;
  if (problemContract && math) math.problemContract = problemContract;
  const alignmentCheck = math && isRecord(math.alignmentCheck) ? { ...math.alignmentCheck } : undefined;
  if (alignmentCheck && math) math.alignmentCheck = alignmentCheck;
  const activeNode = proofPack && isRecord(proofPack.activeNode) ? { ...proofPack.activeNode } : undefined;
  if (activeNode && proofPack) proofPack.activeNode = activeNode;

  trimText(candidate, 'title', 1_024);
  trimText(candidate, 'objective', 8_192);
  trimText(proofPack, 'strategySketch', 4_096);
  trimText(proofPack, 'leanSkeleton', 4_096);
  trimText(activeNode, 'informalClaim', 4_096);
  trimText(activeNode, 'provisionalLeanStatement', 8_192);
  trimText(problemContract, 'informalStatement', 4_096);
  trimText(problemContract, 'formalStatement', 8_192);
  trimText(problemContract, 'formalNegationStatement', 4_096);
  trimText(problemContract, 'officialVerificationCommand', 2_048);
  trimText(alignmentCheck, 'goalInOwnWords', 2_048);
  trimText(alignmentCheck, 'officialVerificationCommand', 2_048);
  trimText(falsificationPlan, 'hypothesis', 2_048);
  trimText(falsificationPlan, 'test', 2_048);
  trimText(falsificationPlan, 'failureSignal', 2_048);
  trimText(candidate, 'roleInstructions', 2_048);
  const dropField = (container: Record<string, unknown> | undefined, key: string): void => {
    if (serializedBytes() > MAX_PROJECTED_CONTEXT_BYTES && container) {
      if (container === math && key === 'researchContract' && durableResearchContract) {
        noteResearchOmission(key, durableResearchContract);
        for (const [field, value] of Object.entries(durableResearchContract)) {
          if (field === 'problemId' || field === 'objective') continue;
          noteResearchOmission(field, value);
        }
      }
      if (container === researchContract) noteResearchOmission(key, container[key]);
      delete container[key];
    }
  };
  // These are useful annotations, but never worth exceeding the transport
  // budget after the active objective and proof identity have been retained.
  dropField(candidate, 'evidenceRefs');
  dropField(candidate, 'acceptanceCriteria');
  dropField(candidate, 'failureCriteria');
  dropField(math, 'applicableLessons');
  // A formal proof repair needs the first diagnostic and next objective to
  // continue the same solver episode. Advisory/review projections may still
  // omit this archive because they have no active repair state.
  if (math?.stage !== 'formalize') dropField(math, 'failureLedger');
  dropField(math, 'researchContract');

  if (math && durableResearchContract && Object.keys(omittedResearchCounts).length > 0) {
    const problemId =
      typeof durableResearchContract.problemId === 'string'
        ? durableResearchContract.problemId
        : typeof math.problemId === 'string'
          ? math.problemId
          : undefined;
    if (problemId) {
      const recovery: MathematicsWorkerContextRecovery = {
        schema: 'deepscientist.mathematics.worker-context-recovery.v1',
        source: 'math_research',
        action: 'get',
        request: {
          problemId,
          assignmentId: typeof candidate.assignmentId === 'string' ? candidate.assignmentId : '',
          command: { action: 'get', limit: 200 },
        },
        statementHash: typeof math.statementHash === 'string' ? math.statementHash : '',
        routeFingerprint: typeof math.routeFingerprint === 'string' ? math.routeFingerprint : '',
        ...(typeof math.activePlanNodeId === 'string' ? { activePlanNodeId: math.activePlanNodeId } : {}),
        durableResearchContractDigest: mathDigest(canonicalMathJson(durableResearchContract)),
        omittedCounts: { ...omittedResearchCounts },
        omittedDigests: { ...omittedResearchDigests },
        instruction:
          'The research context was compacted for transport. Call math_research with request before choosing the next probe; verify the returned problem, assignment, statement, and route identities against this record.',
      };
      math.contextRecovery = recovery;
    }
  }

  // The normal path above keeps the active proof identity and the most useful
  // context.  If a caller supplied several individually oversized required
  // strings, progressively compact every remaining string leaf in the send
  // copy so the transport invariant still holds without touching durable data.
  if (serializedBytes() > MAX_PROJECTED_CONTEXT_BYTES) {
    const identityKeys = new Set([
      'schema',
      'assignmentId',
      'workflowId',
      'laneId',
      'problemId',
      'statementHash',
      'leanStatementHash',
      'routeFingerprint',
      'activePlanNodeId',
      'baseCommit',
      'headCommit',
      'projectRoot',
      'worktreePath',
      'branch',
      'artifactPaths',
      'actionContract',
      'activeObligation',
      'nextAction',
      'requiredEvidence',
      'failureTransition',
    ]);
    const compactStrings = (value: unknown, stringLimit: number, arrayLimit: number, key?: string): unknown => {
      if (typeof value === 'string') {
        if (key && identityKeys.has(key)) return value;
        return value.length > stringLimit
          ? `${value.slice(0, Math.max(0, stringLimit - 32))}\n...[context compacted]`
          : value;
      }
      if (Array.isArray(value)) {
        const selected =
          key && identityKeys.has(key) ? value : value.length > arrayLimit ? value.slice(-arrayLimit) : value;
        return selected.map((item) => compactStrings(item, stringLimit, arrayLimit, key));
      }
      if (isRecord(value)) {
        const copy: Record<string, unknown> = {};
        for (const [childKey, child] of Object.entries(value)) {
          copy[childKey] = compactStrings(child, stringLimit, arrayLimit, childKey);
        }
        return copy;
      }
      return value;
    };
    for (const [stringLimit, arrayLimit] of [
      [2_048, 64],
      [1_024, 32],
      [512, 16],
      [256, 8],
      [128, 4],
      [64, 1],
    ] as const) {
      if (serializedBytes() <= MAX_PROJECTED_CONTEXT_BYTES) break;
      const compacted = compactStrings(candidate, stringLimit, arrayLimit) as Record<string, unknown>;
      for (const key of Object.keys(candidate)) delete candidate[key];
      Object.assign(candidate, compacted);
    }
  }
  const projectedMath = isRecord(candidate.math) ? candidate.math : undefined;
  const frontierPacket =
    projectedMath && isRecord(projectedMath.frontierPacket) ? projectedMath.frontierPacket : undefined;
  if (frontierPacket) refreshMathematicsProofFrontierPacketHash(frontierPacket);
  if (serializedBytes() > MAX_PROJECTED_CONTEXT_BYTES) {
    throw new Error('Mathematics Worker assignment identity exceeds the 24 KB transport budget');
  }
  return Object.freeze(candidate);
}

function projectResearchContract(contract: NonNullable<ResearchTeamAssignment['math']>['researchContract']) {
  if (!contract) return undefined;
  const queryTokens = mathInsightTokens(contract.activeBottleneck ?? contract.nextAction ?? contract.objective);
  const projectRecentRelevant = (values: readonly string[] | undefined): readonly string[] | undefined => {
    if (!values?.length) return undefined;
    const scored = values.map((value, index) => ({
      value,
      index,
      score: [...mathInsightTokens(value)].filter((token) => queryTokens.has(token)).length,
    }));
    const selected = scored
      .filter(({ score }) => score > 0)
      .toSorted((left, right) => right.score - left.score || right.index - left.index)
      .slice();
    const selectedIndexes = new Set(selected.map(({ index }) => index));
    for (let index = values.length - 1; index >= 0; index -= 1) {
      if (selectedIndexes.has(index)) continue;
      selected.push(scored[index]);
      selectedIndexes.add(index);
    }
    let usedBytes = 0;
    const bounded = selected
      .toSorted((left, right) => left.index - right.index)
      .map(({ value }) => value)
      .filter((value) => {
        if (!fitsProjectedBudget(value, usedBytes, MAX_PROJECTED_CONTEXT_BYTES / 2)) return false;
        usedBytes += Buffer.byteLength(JSON.stringify(value), 'utf8');
        return true;
      });
    return Object.freeze(bounded);
  };
  const ranked = (contract.insights ?? [])
    .map((insight, index) => {
      const text = [insight.claim, ...insight.conditions, insight.failure, insight.repair, insight.usableWhen]
        .filter(Boolean)
        .join(' ');
      const score = [...mathInsightTokens(text)].filter((token) => queryTokens.has(token)).length;
      return { insight, index, score };
    })
    .filter(({ score }) => score > 0)
    .sort((left, right) => right.score - left.score || right.index - left.index)
    .slice()
    .map(({ insight }) => insight);
  let insightBytes = 0;
  const insights = (ranked.length ? ranked : [...(contract.insights ?? [])].reverse())
    .filter((insight) => {
      if (!fitsProjectedBudget(insight, insightBytes, MAX_PROJECTED_CONTEXT_BYTES / 2)) return false;
      insightBytes += Buffer.byteLength(JSON.stringify(insight), 'utf8');
      return true;
    })
    .slice(0, ranked.length ? ranked.length : undefined);
  const {
    knownResults,
    establishedClaims,
    conjectures,
    failedApproaches,
    openObligations,
    evidenceNotes: _evidenceNotes,
    insights: _insights,
    ...base
  } = contract;
  const projectedKnownResults = projectRecentRelevant(knownResults);
  const projectedEstablishedClaims = projectRecentRelevant(establishedClaims);
  const projectedConjectures = projectRecentRelevant(conjectures);
  const projectedFailedApproaches = projectRecentRelevant(failedApproaches);
  const projectedOpenObligations = projectRecentRelevant(openObligations);
  return Object.freeze({
    ...base,
    ...(projectedKnownResults ? { knownResults: projectedKnownResults } : {}),
    ...(projectedEstablishedClaims ? { establishedClaims: projectedEstablishedClaims } : {}),
    ...(projectedConjectures ? { conjectures: projectedConjectures } : {}),
    ...(projectedFailedApproaches ? { failedApproaches: projectedFailedApproaches } : {}),
    ...(projectedOpenObligations ? { openObligations: projectedOpenObligations } : {}),
    ...(insights.length
      ? { insights: Object.freeze(insights) }
      : _evidenceNotes?.length
        ? { evidenceNotes: Object.freeze(_evidenceNotes.slice(-3)) }
        : {}),
  });
}

function mathInsightTokens(value: string): ReadonlySet<string> {
  return new Set(
    value
      .toLowerCase()
      .split(/[^a-z0-9_]+/gu)
      .filter((token) => token.length >= 4)
  );
}

/** Compact message for the Lead; the full result is recovered from its receipt. */
export function projectMathematicsResultForLead(
  result: ResearchTeamResult,
  deliveryId: string,
  targetSlotId?: string
): Readonly<Record<string, unknown>> {
  const base = {
    delivery_id: deliveryId,
    assignment_id: result.assignmentId,
    ...(targetSlotId
      ? {
          integration_item: Object.freeze({
            target_slot_id: targetSlotId,
            delivery_id: deliveryId,
          }),
        }
      : {}),
    lane_id: result.laneId,
    execution_mode: result.executionMode ?? 'artifact',
    summary: result.summary,
    disposition: result.disposition,
    research_follow_up:
      'Relate this result to the original target and current missing implication. Separate verified conclusions from hypotheses. Read its evidence, decide whether to integrate, repair, test or revise the route, and retain the reasoning and next mathematical step in math_research. Dispatch is not evidence of progress.',
  };
  if (result.laneId === 'strategy-exploration') {
    return Object.freeze({
      ...base,
      ...(result.math
        ? {
            math: Object.freeze({
              statementHash: result.math.statementHash,
              routeFingerprint: result.math.routeFingerprint,
              routeDisposition: result.math.routeDisposition,
              nextSingleObjective: result.math.nextSingleObjective,
            }),
          }
        : {}),
      ...(result.mathResearchFinding
        ? { math_research_finding: projectMathResearchFindingForLead(result.mathResearchFinding) }
        : {}),
      ...(result.mathLessons?.length ? { math_lessons: result.mathLessons } : {}),
    });
  }
  if (result.laneId === 'independent-review') {
    return Object.freeze({
      ...base,
      ...(result.mathReview ? { math_review: result.mathReview } : {}),
      ...(result.math?.reviewAction
        ? {
            review_action: result.math.reviewAction.toUpperCase(),
            review_next_step: result.math.nextSingleObjective,
          }
        : {}),
      ...(result.mathLessons?.length ? { math_lessons: result.mathLessons } : {}),
    });
  }
  return Object.freeze({
    ...base,
    git: Object.freeze({
      branch: result.git.branch ?? null,
      headCommit: result.git.headCommit ?? null,
    }),
    ...(result.math
      ? {
          math: Object.freeze({
            statementHash: result.math.statementHash,
            routeFingerprint: result.math.routeFingerprint,
            activePlanNodeId: result.math.activePlanNodeId ?? null,
            routeDisposition: result.math.routeDisposition,
            nextSingleObjective: result.math.nextSingleObjective,
            ...(result.math.sourceProgress
              ? {
                  sourceProgress: Object.freeze({
                    artifactPath: result.math.sourceProgress.artifactPath,
                    changedDeclarationNames: result.math.sourceProgress.changedDeclarationNames,
                  }),
                }
              : {}),
          }),
        }
      : {}),
    ...(result.mathNodeReceipt ? { math_node_receipt: result.mathNodeReceipt } : {}),
    ...(result.mathHelperReceipt ? { math_helper_receipt: result.mathHelperReceipt } : {}),
    ...(result.localGateReceipt ? { local_gate_receipt: result.localGateReceipt } : {}),
    ...(result.mathLessons?.length ? { math_lessons: result.mathLessons } : {}),
  });
}

const LEAD_FINDING_MAX_BYTES = 8 * 1024;
const LEAD_FINDING_MAX_ITEMS = 4;

function compactLeadText(value: string, maximum: number): string {
  if (Buffer.byteLength(JSON.stringify(value), 'utf8') <= maximum) return value;
  const suffix = '\n...[finding compacted]';
  let remaining = maximum - Buffer.byteLength(JSON.stringify(suffix), 'utf8');
  let prefix = '';
  for (const character of value) {
    const bytes = Buffer.byteLength(JSON.stringify(character), 'utf8') - 2;
    if (bytes > remaining) break;
    prefix += character;
    remaining -= bytes;
  }
  return prefix + suffix;
}

/** Keep the Lead wake small; the durable receipt remains the lossless source. */
export function projectMathResearchFindingForLead(finding: MathResearchFinding): Readonly<Record<string, unknown>> {
  const compactList = (values: readonly string[]): readonly string[] =>
    Object.freeze(values.slice(-LEAD_FINDING_MAX_ITEMS).map((value) => compactLeadText(value, 512)));
  const projected: Record<string, unknown> = {
    kind: finding.kind,
    ...(finding.mechanism ? { mechanism: compactLeadText(finding.mechanism, 256) } : {}),
    ...(finding.mainlineImpact ? { mainlineImpact: finding.mainlineImpact } : {}),
    ...(finding.nextProbeKind ? { nextProbeKind: finding.nextProbeKind } : {}),
    ...(finding.bottleneckUpdate
      ? {
          bottleneckUpdate: Object.freeze({
            target: compactLeadText(finding.bottleneckUpdate.target, 512),
            outcome: finding.bottleneckUpdate.outcome,
            ...(finding.bottleneckUpdate.category ? { category: finding.bottleneckUpdate.category } : {}),
            ...(finding.bottleneckUpdate.diagnosis
              ? { diagnosis: compactLeadText(finding.bottleneckUpdate.diagnosis, 768) }
              : {}),
            ...(finding.bottleneckUpdate.repair
              ? { repair: compactLeadText(finding.bottleneckUpdate.repair, 768) }
              : {}),
          }),
        }
      : {}),
    ...(finding.helperRequest
      ? {
          helperRequest: Object.fromEntries(
            Object.entries(finding.helperRequest).map(([key, value]) => [
              key,
              typeof value === 'string' ? compactLeadText(value, 512) : value,
            ])
          ),
        }
      : {}),
    ...(finding.problemFamilyProbe
      ? {
          problemFamilyProbe: Object.freeze({
            ...finding.problemFamilyProbe,
            instances: Object.freeze(finding.problemFamilyProbe.instances.slice(-3)),
            ...(finding.problemFamilyProbe.sharedMechanism
              ? { sharedMechanism: compactLeadText(finding.problemFamilyProbe.sharedMechanism, 768) }
              : {}),
            ...(finding.problemFamilyProbe.firstCounterexample
              ? { firstCounterexample: compactLeadText(finding.problemFamilyProbe.firstCounterexample, 768) }
              : {}),
          }),
        }
      : {}),
    ...(finding.solutionSketchRef ? { solutionSketchRef: finding.solutionSketchRef } : {}),
    summary: compactLeadText(finding.summary, 1_200),
    evidenceRefs: finding.evidenceRefs
      .slice(-LEAD_FINDING_MAX_ITEMS)
      .filter((ref) => Buffer.byteLength(JSON.stringify(ref), 'utf8') <= 512),
    evidenceIndex: finding.evidenceRefs.slice(-LEAD_FINDING_MAX_ITEMS).map((ref) => ({
      id: `evidence-${crypto.createHash('sha256').update(ref).digest('hex')}`,
      durableIndex: finding.evidenceRefs.indexOf(ref),
    })),
    evidenceRetrieval:
      'Read the full finding from the durable delivery identified by delivery_id. Evidence IDs are lookup labels, not verification receipts.',
    projectionOnly: true,
    originalCounts: {
      evidenceRefs: finding.evidenceRefs.length,
      openObligations: finding.openObligations.length,
      establishedClaims: finding.establishedClaims.length,
    },
    establishedClaims: compactList(finding.establishedClaims),
    conjectureUpdates: compactList(finding.conjectureUpdates),
    eliminatedApproaches: compactList(finding.eliminatedApproaches),
    openObligations: compactList(finding.openObligations),
    nextAction: compactLeadText(finding.nextAction, 800),
  };
  if (Buffer.byteLength(JSON.stringify(projected), 'utf8') <= LEAD_FINDING_MAX_BYTES) {
    return Object.freeze(projected);
  }
  delete projected.conjectureUpdates;
  delete projected.establishedClaims;
  projected.omittedFields = ['conjectureUpdates', 'establishedClaims'];
  if (Buffer.byteLength(JSON.stringify(projected), 'utf8') > LEAD_FINDING_MAX_BYTES) {
    delete projected.problemFamilyProbe;
    projected.omittedFields = [...(projected.omittedFields as string[]), 'problemFamilyProbe'];
  }
  if (Buffer.byteLength(JSON.stringify(projected), 'utf8') > LEAD_FINDING_MAX_BYTES) {
    projected.evidenceRefs = [];
    projected.eliminatedApproaches = compactList(finding.eliminatedApproaches.slice(-1));
    projected.openObligations = compactList(finding.openObligations.slice(-2));
    delete projected.solutionSketchRef;
    projected.omittedFields = [...(projected.omittedFields as string[]), 'evidenceRefs', 'solutionSketchRef'];
    projected.reducedLists = ['eliminatedApproaches', 'openObligations'];
  }
  return Object.freeze(projected);
}

function selectApplicableLessons(
  values: readonly MathLesson[],
  routeFingerprint: string,
  routePattern: string | undefined
): readonly MathLesson[] {
  const pattern = routePattern?.trim().toLowerCase().replace(/\s+/gu, ' ');
  const selected: Array<{ lesson: MathLesson; relevance: number }> = [];
  const compare = (
    left: { lesson: MathLesson; relevance: number },
    right: { lesson: MathLesson; relevance: number }
  ): number => left.relevance - right.relevance || right.lesson.createdAt - left.lesson.createdAt;
  for (const lesson of values) {
    let relevance = 3;
    if (lesson.routeFingerprint === routeFingerprint) relevance = 0;
    else if (
      lesson.disposition === 'avoid_pattern' &&
      pattern &&
      lesson.failedPattern.trim().toLowerCase().replace(/\s+/gu, ' ') === pattern
    ) {
      relevance = 1;
    } else if (lesson.disposition === 'avoid_pattern') {
      relevance = 2;
    }
    const candidate = { lesson, relevance };
    let insertionIndex = selected.length;
    while (insertionIndex > 0 && compare(candidate, selected[insertionIndex - 1]) < 0) insertionIndex -= 1;
    selected.splice(insertionIndex, 0, candidate);
  }
  let usedBytes = 0;
  const bounded = selected
    .map(({ lesson }) => lesson)
    .filter((lesson) => {
      if (!fitsProjectedBudget(lesson, usedBytes)) return false;
      usedBytes += Buffer.byteLength(JSON.stringify(lesson), 'utf8');
      return true;
    });
  return Object.freeze(bounded);
}

function projectFailureLedger(ledger: MathFailureLedger): Readonly<Record<string, unknown>> {
  const fitStrings = (values: readonly string[], required?: string): readonly string[] => {
    let usedBytes = 0;
    const selected: string[] = [];
    if (required && fitsProjectedBudget(required, usedBytes, MAX_PROJECTED_CONTEXT_BYTES / 3)) {
      selected.push(required);
      usedBytes += Buffer.byteLength(JSON.stringify(required), 'utf8');
    }
    const historical: string[] = [];
    for (let index = values.length - 1; index >= 0; index -= 1) {
      const value = values[index];
      if (value === required || historical.includes(value)) continue;
      if (!fitsProjectedBudget(value, usedBytes, MAX_PROJECTED_CONTEXT_BYTES / 3)) continue;
      historical.push(value);
      usedBytes += Buffer.byteLength(JSON.stringify(value), 'utf8');
    }
    selected.push(...historical.reverse());
    return Object.freeze(selected);
  };
  return Object.freeze({
    ...ledger,
    triedRoutes: fitStrings(ledger.triedRoutes, ledger.activeRoute),
    doNotRepeatRefs: fitStrings(ledger.doNotRepeatRefs),
  });
}

function projectDoNotRepeat(values: readonly string[], lessons: readonly MathLesson[]): readonly string[] {
  const lessonRefs: string[] = [];
  const seen = new Set<string>();
  for (const lesson of lessons) {
    const reference = `lesson:${lesson.lessonId}`;
    if (seen.has(reference)) continue;
    seen.add(reference);
    lessonRefs.push(reference);
  }
  const historicalRefs: string[] = [];
  for (let index = values.length - 1; index >= 0; index -= 1) {
    const reference = values[index];
    if (seen.has(reference)) continue;
    seen.add(reference);
    historicalRefs.push(reference);
  }
  historicalRefs.reverse();
  // The newest failed routes are the immediate repair context.  Select them
  // first, then spend whatever remains on lesson references.  Return lessons
  // first so the newest historical reference remains the final entry, which
  // also makes the ordering useful to a human inspecting a compact payload.
  let usedBytes = 0;
  const selectedHistorical: string[] = [];
  for (let index = historicalRefs.length - 1; index >= 0; index -= 1) {
    const reference = historicalRefs[index];
    if (!fitsProjectedBudget(reference, usedBytes, MAX_PROJECTED_CONTEXT_BYTES / 3)) continue;
    selectedHistorical.push(reference);
    usedBytes += Buffer.byteLength(JSON.stringify(reference), 'utf8');
  }
  selectedHistorical.reverse();
  const selectedLessons: string[] = [];
  for (const reference of lessonRefs) {
    if (!fitsProjectedBudget(reference, usedBytes, MAX_PROJECTED_CONTEXT_BYTES / 3)) continue;
    selectedLessons.push(reference);
    usedBytes += Buffer.byteLength(JSON.stringify(reference), 'utf8');
  }
  return Object.freeze([...selectedLessons, ...selectedHistorical]);
}

function createActiveNodeProofPack(
  card: MathRouteCard,
  activePlanNodeId: string,
  failureLedger?: MathFailureLedger,
  solutionSketchRef?: string,
  problemId?: string
): MathActiveNodeProofPack {
  const nodeById = new Map<string, MathPlanNode>();
  for (const node of card.planNodes) nodeById.set(node.id, node);
  const activeNode = nodeById.get(activePlanNodeId);
  if (!activeNode) throw new Error('Mathematics active proof-pack node is absent from the selected route');
  const dependencyIds = new Set<string>();
  const visitDependencies = (node: MathPlanNode): void => {
    for (const dependencyId of node.dependsOn) {
      if (dependencyIds.has(dependencyId)) continue;
      dependencyIds.add(dependencyId);
      const dependency = nodeById.get(dependencyId);
      if (dependency) visitDependencies(dependency);
    }
  };
  visitDependencies(activeNode);
  const relevantNodeIds = new Set(dependencyIds);
  relevantNodeIds.add(activePlanNodeId);
  const dependencyNodes: MathPlanNode[] = [];
  for (const node of card.planNodes) {
    if (dependencyIds.has(node.id)) dependencyNodes.push(node);
  }
  const premiseCoverage: Array<MathRouteCard['premiseBundle']['coverage'][number]> = [];
  const premiseNames = new Set<string>();
  for (const entry of card.premiseBundle.coverage) {
    if (!relevantNodeIds.has(entry.planNodeId)) continue;
    premiseCoverage.push(entry);
    for (const premiseName of entry.premiseDeclarationNames) premiseNames.add(premiseName);
  }
  const premises = card.premiseBundle.premises.filter((premise) => premiseNames.has(premise.declarationName));
  const premiseHints = selectGoalAlignedPremiseHints(card, activeNode, premiseNames, failureLedger);
  return Object.freeze({
    statementHash: card.statementHash,
    routeFingerprint: card.routeFingerprint,
    activePlanNodeId,
    activeNode,
    strategySketch: card.premiseBundle.strategySketch,
    leanSkeleton: card.premiseBundle.leanSkeleton,
    ...(solutionSketchRef ? { solutionSketchRef } : {}),
    dependencyNodes: Object.freeze(dependencyNodes),
    bridges: Object.freeze(
      card.bridges.filter(
        (bridge) => relevantNodeIds.has(bridge.dependencyNodeId) && relevantNodeIds.has(bridge.consumerNodeId)
      )
    ),
    premises: Object.freeze(premises),
    premiseHints,
    ...(problemId
      ? {
          premiseRetrieval: Object.freeze({
            tool: 'math_portfolio' as const,
            action: 'get' as const,
            problemId,
            routeFingerprint: card.routeFingerprint,
            planNodeId: activePlanNodeId,
            premiseLimit: 4 as const,
            goalSource: 'live_lean_goal' as const,
            importModulesSource: 'current_lean_file' as const,
            sourceFileSource: 'current_lean_file' as const,
            cacheBy: 'proof_state_fingerprint' as const,
            upstreamSources: Object.freeze(['leansearch', 'loogle'] as const),
            upstreamActivation: 'after_local_miss' as const,
          }),
        }
      : {}),
    premiseCoverage: Object.freeze(premiseCoverage),
  });
}

function selectGoalAlignedPremiseHints(
  card: MathRouteCard,
  activeNode: MathPlanNode,
  usedPremiseNames: ReadonlySet<string>,
  failureLedger?: MathFailureLedger
): MathRouteCard['premiseBundle']['premises'] {
  const query = [
    activeNode.informalClaim,
    activeNode.provisionalLeanStatement,
    failureLedger?.firstLeanError,
    failureLedger?.nextSingleObjective,
  ]
    .filter(Boolean)
    .join(' ')
    .toLowerCase();
  const queryTokens = new Set(query.split(/[^a-z0-9_]+/gu).filter((token) => token.length >= 4));
  if (!queryTokens.size) return Object.freeze([]);
  const ranked = card.premiseBundle.premises
    .filter((premise) => premise.status !== 'rejected' && !usedPremiseNames.has(premise.declarationName))
    .map((premise) => {
      const searchable =
        `${premise.declarationName} ${premise.intendedUse} ${premise.sourceModule ?? ''}`.toLowerCase();
      const score = searchable
        .split(/[^a-z0-9_]+/gu)
        .filter((token) => token.length >= 4 && queryTokens.has(token)).length;
      return { premise, score };
    })
    .filter(({ score }) => score > 0)
    .sort((left, right) => right.score - left.score);
  return Object.freeze(ranked.slice(0, 4).map(({ premise }) => premise));
}

function assignmentProjectionEfficiency(
  assignment: Readonly<Record<string, unknown>> | ResearchTeamAssignment,
  assignmentPayloadBytes: number,
  fullAssignmentBytes: number
): MathematicsAssignmentProjectionEfficiency {
  const math = isRecord(assignment.math) ? assignment.math : undefined;
  const proofPack = isRecord(math?.proofPack) ? math.proofPack : undefined;
  const proofPackPremises = Array.isArray(proofPack?.premises) ? proofPack.premises.length : 0;
  const proofPackHints = Array.isArray(proofPack?.premiseHints) ? proofPack.premiseHints.length : 0;
  const proofPackDependencies = Array.isArray(proofPack?.dependencyNodes) ? proofPack.dependencyNodes.length : 0;
  let routeCardsInjected = 0;
  let routePremisesInjected = 0;
  for (const card of Array.isArray(math?.routeCards) ? math.routeCards : []) {
    if (!isRecord(card)) continue;
    routeCardsInjected += 1;
    if (isRecord(card.premiseBundle) && Array.isArray(card.premiseBundle.premises)) {
      routePremisesInjected += card.premiseBundle.premises.length;
    }
  }
  return Object.freeze({
    assignment_payload_bytes: assignmentPayloadBytes,
    full_assignment_bytes: fullAssignmentBytes,
    projection_ratio: fullAssignmentBytes ? assignmentPayloadBytes / fullAssignmentBytes : 1,
    route_cards_injected: routeCardsInjected,
    proof_pack_nodes_injected: proofPack ? proofPackDependencies + 1 : 0,
    lessons_injected: Array.isArray(math?.applicableLessons) ? math.applicableLessons.length : 0,
    premises_injected: proofPackPremises + proofPackHints + routePremisesInjected,
  });
}

export function validateDurableResearchTeamAssignment(
  value: unknown,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  validateAssignment: DurableAssignmentValidator
): ResearchTeamAssignment {
  if (!isRecord(value)) throw new Error('Durable Research Team assignment receipt is malformed');
  if (
    isRecord(value.git) &&
    (value.git.branch !== undefined || value.git.worktreePath !== undefined || value.git.headCommit !== undefined)
  ) {
    throw new Error('Durable Research Team assignment contains prepared Git delivery fields');
  }
  return validateAssignment(value, capability, target);
}

export function hydrateMathematicsWorkerResult(
  value: Record<string, unknown>,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  readAssignment: AssignmentReader | undefined,
  validateAssignment: DurableAssignmentValidator,
  resolveCommit?: PreparedCommitResolver
): Record<string, unknown> {
  if (capability.profileId !== 'mathematics-research-team') return value;
  const normalizedWorkerAction = normalizeMathematicsWorkerAction(value.action);
  // Source progress is runtime-only. If a durable assignment cannot be read,
  // remove any Worker-supplied copy instead of allowing it into validation.
  if (!readAssignment) return stripWorkerSourceProgress(value);
  const assignmentId = typeof value.assignmentId === 'string' ? value.assignmentId.trim() : '';
  if (!assignmentId) return stripWorkerSourceProgress(value);
  const receipt = readAssignment({
    workspace: capability.projectRoot,
    teamId: capability.teamId,
    slotId: target.slotId,
    assignmentId,
  });
  if (!receipt || (receipt.state !== 'accepted' && receipt.state !== 'integrated')) {
    return stripWorkerSourceProgress(value);
  }
  const assignment = resolveMathematicsResearchAssignment(
    validateDurableResearchTeamAssignment(receipt.assignment, capability, target, validateAssignment),
    capability,
    target,
    receipt.assignment
  );
  const priorDeliveryResult = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
  const producedAt =
    typeof value.producedAt === 'string'
      ? value.producedAt
      : typeof priorDeliveryResult?.producedAt === 'string'
        ? priorDeliveryResult.producedAt
        : new Date().toISOString();
  const rawGit = isRecord(value.git) ? value.git : undefined;
  const headCommit = hydratePreparedHeadCommit(rawGit?.headCommit, priorDeliveryResult, receipt, resolveCommit);
  const git = isRecord(value.git)
    ? Object.freeze({
        ...value.git,
        projectRoot: assignment.git.projectRoot,
        baseCommit: assignment.git.baseCommit,
        ...(target.laneId === 'lean-engineering' && receipt.preparedGit?.branch
          ? { branch: receipt.preparedGit.branch }
          : {}),
        ...(target.laneId === 'lean-engineering' && receipt.preparedGit?.worktreePath
          ? { worktreePath: receipt.preparedGit.worktreePath }
          : {}),
        ...(headCommit ? { headCommit } : {}),
      })
    : value.git === undefined
      ? Object.freeze({
          projectRoot: assignment.git.projectRoot,
          baseCommit: assignment.git.baseCommit,
          ...(target.laneId === 'lean-engineering' && receipt.preparedGit?.branch
            ? { branch: receipt.preparedGit.branch }
            : {}),
          ...(target.laneId === 'lean-engineering' && receipt.preparedGit?.worktreePath
            ? { worktreePath: receipt.preparedGit.worktreePath }
            : {}),
        })
      : value.git;
  const frozenReviewReceipt = assignment.math?.stage === 'review' ? assignment.math.localGateReceipt : undefined;
  const isRouteSelectionStage = assignment.math?.stage === 'diversify' || assignment.math?.stage === 'replan';
  const mathRouteCard =
    isRouteSelectionStage && isRecord(value.mathRouteCard)
      ? hydrateMathRouteCard(assignment, capability, target, value.mathRouteCard)
      : value.mathRouteCard;
  const mathResearchFinding =
    isRouteSelectionStage && isRecord(value.mathResearchFinding)
      ? sanitizeOptionalMathResearchFindingCategory(value.mathResearchFinding)
      : undefined;
  const mathReview =
    frozenReviewReceipt && isRecord(value.mathReview)
      ? Object.freeze({
          targetCommit: frozenReviewReceipt.targetCommit,
          statementHash: assignment.math?.statementHash,
          localGateReceiptId: frozenReviewReceipt.receiptId,
          ...value.mathReview,
          problemId: assignment.math?.problemContract?.problemId,
          reviewerSessionId: `${capability.teamId}:${target.slotId}:${assignment.assignmentId}`,
        })
      : value.mathReview;
  const reviewRuntime =
    frozenReviewReceipt && isRecord(mathReview)
      ? deriveMathReviewRuntime(assignment, frozenReviewReceipt, mathReview)
      : undefined;
  const routeRuntime =
    isRecord(mathRouteCard) &&
    value.math === undefined &&
    (value.disposition === undefined || value.disposition === 'accepted')
      ? deriveMathRouteRuntime(assignment, mathRouteCard)
      : undefined;
  const findingRuntime =
    mathResearchFinding && value.math === undefined
      ? deriveMathResearchFindingRuntime(assignment, mathResearchFinding)
      : undefined;
  const leanRuntime =
    target.laneId === 'lean-engineering' && assignment.math?.stage === 'formalize'
      ? deriveMathLeanRuntime(assignment, value)
      : undefined;
  const explorerMath =
    target.laneId === 'strategy-exploration' && isRouteSelectionStage && isRecord(value.math)
      ? hydrateMathExplorerProgress(value.math)
      : value.math;
  // Candidate review progress is reconstructed from the frozen receipt and
  // normalized verdict. Never let a reviewer-provided `math` object override
  // the runtime-owned action, route disposition, or evidence boundary.
  const math =
    target.laneId === 'independent-review' && reviewRuntime
      ? reviewRuntime.math
      : isRecord(explorerMath)
        ? (leanRuntime?.math ?? explorerMath)
        : value.math === undefined
          ? (leanRuntime?.math ?? routeRuntime?.math ?? findingRuntime?.math)
          : undefined;
  // executionPolicy is runtime-owned. A Worker may omit it from a compact
  // delivery, but omission must not erase the cursor that was bound to the
  // assignment and persisted in the WAL.
  const mathWithExecutionPolicy: Readonly<Record<string, unknown>> | undefined =
    math && assignment.math?.executionPolicy && !isRecord(math.executionPolicy)
      ? (Object.freeze({ ...math, executionPolicy: assignment.math.executionPolicy }) as Readonly<
          Record<string, unknown>
        >)
      : math;
  // Compare committed artifact source after Git identity has been recovered.
  // Any Worker-supplied sourceProgress is discarded below and can never pass
  // through as runtime evidence.
  const runtimeSourceProgress =
    target.laneId === 'lean-engineering' && assignment.math?.stage === 'formalize' && isRecord(git)
      ? deriveMathematicsSourceProgress(assignment, git, receipt.preparedGit)
      : undefined;
  const explorerCheckpoint =
    target.laneId === 'strategy-exploration' &&
    isRouteSelectionStage &&
    mathWithExecutionPolicy &&
    isRecord(value.mathCheckpoint)
      ? hydrateMathCheckpoint(assignment, mathWithExecutionPolicy, value.mathCheckpoint)
      : undefined;
  const leanCheckpoint =
    leanRuntime && mathWithExecutionPolicy && isRecord(value.mathCheckpoint) && isRecord(git)
      ? hydrateMathCheckpoint(
          assignment,
          mathWithExecutionPolicy,
          value.mathCheckpoint,
          typeof git.headCommit === 'string' ? git.headCommit : assignment.git.baseCommit
        )
      : undefined;
  const hydratedMathCheckpoint =
    leanCheckpoint ??
    explorerCheckpoint ??
    (reviewRuntime?.mathCheckpoint && value.mathCheckpoint === undefined ? reviewRuntime.mathCheckpoint : undefined);
  const checkpointWithReceipt =
    hydratedMathCheckpoint && isRecord(value.mathHelperReceipt) && typeof value.mathHelperReceipt.receiptId === 'string'
      ? Object.freeze({
          ...hydratedMathCheckpoint,
          ledger: Object.freeze({
            ...(isRecord(hydratedMathCheckpoint.ledger) ? hydratedMathCheckpoint.ledger : {}),
            latestReceipt: value.mathHelperReceipt.receiptId,
          }),
        })
      : hydratedMathCheckpoint;
  const mathLessons =
    hydratedMathCheckpoint && Array.isArray(value.mathLessons)
      ? value.mathLessons.filter((lesson): lesson is Record<string, unknown> => isRecord(lesson))
      : undefined;
  const planBefore = assignmentMathPlanSnapshot(assignment, {
    ...(isRecord(value.math) ? value.math : {}),
    ...(isRecord(value.mathHelperReceipt) ? { mathHelperReceipt: value.mathHelperReceipt } : {}),
  });
  // The route card is frozen in the durable assignment.  Worker-supplied DAG
  // snapshots are only hints and must not be allowed to replace that source
  // of truth (a restarted or compromised Worker could otherwise move the
  // frontier or mark arbitrary nodes as verified).  Always derive the post
  // snapshot from the trusted route card and the verified-node delta.
  const planAfter =
    math && planBefore
      ? applyMathPlanVerificationDelta(planBefore, math, value, assignment.math?.proofState)
      : undefined;
  const mathWithoutWorkerPlan = mathWithExecutionPolicy
    ? (({ planBefore: _planBefore, planAfter: _planAfter, ...progress }) => progress)(mathWithExecutionPolicy)
    : undefined;
  const bindLeanStatementHash = (receipt: unknown): unknown => {
    if (!isRecord(receipt) || !assignment.math?.problemContract?.leanStatementHash) return receipt;
    const claim = receipt.claim === 'negation' ? 'negation' : 'statement';
    const expected =
      claim === 'negation'
        ? assignment.math.problemContract.leanNegationHash
        : assignment.math.problemContract.leanStatementHash;
    if (!expected) {
      throw new Error('Worker mathematics negation receipt has no immutable formal negation contract');
    }
    if (receipt.leanStatementHash !== undefined && receipt.leanStatementHash !== expected) {
      throw new Error(`Worker mathematics ${claim} receipt leanStatementHash does not match the immutable contract`);
    }
    return Object.freeze({ ...receipt, leanStatementHash: expected });
  };
  const boundLocalGateReceipt = bindLeanStatementHash(
    frozenReviewReceipt || (isRecord(value.localGateReceipt) ? value.localGateReceipt : undefined)
  );
  // A node receipt is bound to the node's provisional Lean declaration, not
  // to the final problem declaration.  Do not stamp the whole-problem hash on
  // an intermediate lemma receipt.
  const boundMathNodeReceipt = value.mathNodeReceipt;
  const trustedMath = mathWithoutWorkerPlan
    ? (() => {
        const {
          progressFingerprint: _workerProgressFingerprint,
          sourceProgress: _workerSourceProgress,
          ...progressWithoutFingerprint
        } = mathWithoutWorkerPlan;
        const hydrated = {
          statementHash: assignment.math?.statementHash,
          routeFingerprint: assignment.math?.routeFingerprint,
          ...(assignment.math?.activePlanNodeId ? { activePlanNodeId: assignment.math.activePlanNodeId } : {}),
          ...progressWithoutFingerprint,
          ...(runtimeSourceProgress ? { sourceProgress: runtimeSourceProgress } : {}),
          ...(planBefore ? { planBefore } : {}),
          ...(planAfter ? { planAfter } : {}),
        };
        return Object.freeze({
          ...hydrated,
          progressFingerprint: deriveMathProgressFingerprint(
            hydrated,
            deriveMathReceiptFingerprintIdentity([boundLocalGateReceipt, boundMathNodeReceipt, value.mathHelperReceipt])
          ),
        });
      })()
    : undefined;
  const runtimeDisposition =
    runtimeSourceProgress &&
    assignment.math?.stage === 'formalize' &&
    (typeof math?.routeDisposition !== 'string' || math.routeDisposition !== 'reject')
      ? 'accepted'
      : (leanRuntime?.disposition ??
        reviewRuntime?.disposition ??
        routeRuntime?.disposition ??
        findingRuntime?.disposition);
  const expectedAssignmentBinding = expectedResearchTeamAssignmentBinding(assignment);
  const assignmentBinding =
    value.assignmentBinding === undefined
      ? expectedAssignmentBinding
      : isRecord(value.assignmentBinding)
        ? Object.freeze({ ...expectedAssignmentBinding, ...value.assignmentBinding })
        : value.assignmentBinding;
  return Object.freeze({
    schema: RESEARCH_TEAM_RESULT_SCHEMA,
    workflowId: assignment.workflowId,
    laneId: assignment.laneId,
    executionMode: assignment.executionMode ?? 'artifact',
    producedAt,
    ...(value.disposition === undefined && runtimeDisposition ? { disposition: runtimeDisposition } : {}),
    ...value,
    ...(runtimeDisposition === 'accepted' ? { disposition: 'accepted' as const } : {}),
    assignmentBinding,
    ...(boundLocalGateReceipt ? { localGateReceipt: boundLocalGateReceipt } : {}),
    ...(boundMathNodeReceipt ? { mathNodeReceipt: boundMathNodeReceipt } : {}),
    ...(mathReview !== undefined ? { mathReview } : {}),
    ...(mathRouteCard !== undefined ? { mathRouteCard } : {}),
    ...(mathResearchFinding !== undefined ? { mathResearchFinding } : {}),
    mathLessons: mathLessons?.length ? mathLessons : undefined,
    ...(checkpointWithReceipt ? { mathCheckpoint: checkpointWithReceipt } : {}),
    git,
    ...(trustedMath ? { math: trustedMath } : {}),
    ...(normalizedWorkerAction ? { action: normalizedWorkerAction } : {}),
  });
}

function stripWorkerSourceProgress(value: Record<string, unknown>): Record<string, unknown> {
  if (!isRecord(value.math) || !Object.prototype.hasOwnProperty.call(value.math, 'sourceProgress')) return value;
  const { sourceProgress: _sourceProgress, ...math } = value.math;
  return Object.freeze({ ...value, math: Object.freeze(math) });
}

function sanitizeOptionalMathResearchFindingCategory(
  finding: Record<string, unknown>
): Readonly<Record<string, unknown>> {
  if (!isRecord(finding.bottleneckUpdate)) return finding;
  const category = finding.bottleneckUpdate.category;
  if (category === undefined || MATH_FAILURE_CATEGORIES.some((candidate) => candidate === category)) return finding;
  const { category: _invalidCategory, ...bottleneckUpdate } = finding.bottleneckUpdate;
  return Object.freeze({ ...finding, bottleneckUpdate: Object.freeze(bottleneckUpdate) });
}

function hydratePreparedHeadCommit(
  value: unknown,
  priorDeliveryResult: Record<string, unknown> | undefined,
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  resolveCommit: PreparedCommitResolver | undefined
): string | undefined {
  if (typeof value !== 'string') return undefined;
  const reference = value.trim();
  if (FULL_GIT_OBJECT_ID.test(reference) || !SHORT_GIT_OBJECT_ID.test(reference)) return reference;

  const priorGit = isRecord(priorDeliveryResult?.git) ? priorDeliveryResult.git : undefined;
  const priorHead = typeof priorGit?.headCommit === 'string' ? priorGit.headCommit : '';
  if (FULL_GIT_OBJECT_ID.test(priorHead) && priorHead.startsWith(reference)) return priorHead;

  const worktreePath = receipt.preparedGit?.worktreePath;
  if (!worktreePath || !resolveCommit) return reference;
  const resolved = resolveCommit({ workspace: worktreePath, reference });
  if (!FULL_GIT_OBJECT_ID.test(resolved) || !resolved.startsWith(reference)) {
    throw new Error('Prepared Worker commit resolution returned an unexpected Git object id');
  }
  return resolved;
}

/** Project an accepted route over the immutable dispatch without changing its ownership or statement. */
export function resolveMathematicsResearchAssignment(
  assignment: ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  persistedAssignment: unknown = assignment,
  env: NodeJS.ProcessEnv = process.env
): ResearchTeamAssignment {
  const problemId = assignment.math?.problemContract?.problemId ?? assignment.math?.researchContract?.problemId;
  if (capability.profileId !== 'mathematics-research-team' || !problemId) return assignment;
  if (isMathLiteRunEnvironment(env)) return assignment;
  const workflow = readMathResearchWorkflowState(capability.projectRoot, problemId, assignment.assignmentId, env);
  if (!workflow) return assignment;
  if (
    workflow.binding.teamId !== capability.teamId ||
    workflow.binding.slotId !== target.slotId ||
    workflow.binding.workerId !== target.roleId ||
    workflow.binding.statementHash !== assignment.math?.statementHash ||
    workflow.binding.initialRouteFingerprint !== assignment.math.routeFingerprint ||
    workflow.binding.assignmentDigest !== mathDigest(canonicalMathJson(persistedAssignment))
  ) {
    throw new Error('Research route does not match the immutable assignment binding.');
  }
  if (workflow.pending) throw new Error('The main-route proposal requires a Lead decision before delivery.');
  if (workflow.route.revision === 0) return assignment;
  if (
    !workflow.binding.routeRevisionsSupported ||
    !assignment.math.directAttempt ||
    assignment.math.stage !== 'formalize' ||
    assignment.math.routeCards?.length ||
    assignment.math.proofPlan
  ) {
    throw new Error('This assignment adapter does not support in-place main-route revisions.');
  }
  return Object.freeze({
    ...assignment,
    objective: workflow.route.objective,
    math: Object.freeze({ ...assignment.math, routeFingerprint: workflow.route.fingerprint }),
  });
}

export function expectedResearchTeamAssignmentBinding(
  assignment: ResearchTeamAssignment
): ResearchTeamAssignmentBinding {
  return Object.freeze({
    assignmentId: assignment.assignmentId,
    workflowId: assignment.workflowId,
    laneId: assignment.laneId,
    baseCommit: assignment.git.baseCommit,
    ...(assignment.math
      ? {
          stage: assignment.math.stage,
          workflowStage: assignment.math.workflowStage,
          statementHash: assignment.math.statementHash,
          routeFingerprint: assignment.math.routeFingerprint,
          ...(assignment.math.activePlanNodeId ? { activePlanNodeId: assignment.math.activePlanNodeId } : {}),
          ...(assignment.math.localGateReceipt
            ? { localGateReceiptId: assignment.math.localGateReceipt.receiptId }
            : {}),
          ...(assignment.math.stage === 'official_gate' && assignment.math.problemContract
            ? { officialVerificationCommand: assignment.math.problemContract.officialVerificationCommand }
            : {}),
        }
      : {}),
  });
}

export function classifyResearchTeamMathProgress(result: ResearchTeamResult): ReturnType<typeof classifyMathProgress> {
  if (!result.math) return 'stalled';
  const context = {
    // Lean Workers may report tactic-state deltas without a terminal receipt;
    // declaration/node claims are only frontier progress when the runtime
    // supplied a stored kernel receipt. Advisory route exploration remains
    // trusted to classify its library-fact and route evidence normally.
    kernelReceiptBound:
      result.laneId !== 'lean-engineering' ||
      Boolean(result.localGateReceipt || result.mathNodeReceipt || result.mathHelperReceipt),
    requireKernelReceiptForPlanExpansion: result.laneId === 'lean-engineering',
  } as const;
  const kind = classifyMathProgressKind(result.math, context);
  const outcome =
    kind === 'infra_progress'
      ? 'infra_failed'
      : [
            'kernel_progress',
            'foundation_progress',
            'goal_progress',
            'route_information',
            'research_information',
          ].includes(kind)
        ? 'advanced'
        : 'stalled';
  return outcome === 'stalled' &&
    result.laneId === 'strategy-exploration' &&
    ['diversify', 'replan'].includes(result.assignmentBinding?.stage ?? '') &&
    (result.mathRouteCard || result.mathResearchFinding) &&
    result.math.routeDisposition === 'advance'
    ? 'advanced'
    : outcome;
}

function deriveMathResearchFindingRuntime(
  assignment: ResearchTeamAssignment,
  finding: Readonly<Record<string, unknown>>
): Readonly<{ disposition: 'accepted' | 'refuted'; math: Readonly<Record<string, unknown>> }> {
  const evidenceRefs = Array.isArray(finding.evidenceRefs)
    ? finding.evidenceRefs.filter((value): value is string => typeof value === 'string' && Boolean(value.trim()))
    : [];
  const routeRefuted = finding.mainlineImpact === 'route_refuted';
  return Object.freeze({
    disposition: routeRefuted ? 'refuted' : 'accepted',
    math: createMathRuntimeProgress(assignment, {
      routeDisposition: routeRefuted ? 'reject' : 'advance',
      nextSingleObjective: String(finding.nextAction || 'Choose the next highest-information research action.'),
      evidenceDelta: routeRefuted
        ? [
            Object.freeze({
              kind: 'route_refutation',
              ref: evidenceRefs[0] || `research-finding:${assignment.assignmentId}`,
              summary: String(finding.summary || 'The active route was refuted.'),
            }),
          ]
        : [
            Object.freeze({
              kind: String(finding.kind || 'critique'),
              ref: evidenceRefs[0] || `research-finding:${assignment.assignmentId}`,
              summary: String(finding.summary || 'Research state updated.'),
            }),
          ],
    }),
  });
}

function createMathRuntimeProgress(
  assignment: ResearchTeamAssignment,
  input: Readonly<{
    routeDisposition: 'advance' | 'reject';
    reviewAction?: 'advance' | 'repair' | 'reject';
    nextSingleObjective: string;
    checkedDeclarationsAdded?: number;
    evidenceDelta?: readonly Readonly<Record<string, unknown>>[];
  }>
): Readonly<Record<string, unknown>> {
  const progress = {
    statementHash: assignment.math?.statementHash,
    routeFingerprint: assignment.math?.routeFingerprint,
    checkedDeclarationsAdded: input.checkedDeclarationsAdded ?? 0,
    openGoalCountBefore: 0,
    openGoalCountAfter: 0,
    evidenceDelta: Object.freeze(input.evidenceDelta ?? []),
    routeDisposition: input.routeDisposition,
    ...(input.reviewAction ? { reviewAction: input.reviewAction } : {}),
    nextSingleObjective: input.nextSingleObjective,
    infraStatus: 'ready',
  } satisfies Record<string, unknown>;
  return Object.freeze({ ...progress, progressFingerprint: deriveMathProgressFingerprint(progress) });
}

/**
 * Build a stable identity for the proof frontier.  Commit ids and prose
 * objectives are intentionally excluded: a new commit that leaves the first
 * goal/error untouched must remain a stall after a Lead restart.
 */
export function deriveMathProgressFingerprint(
  value: Readonly<Record<string, unknown>>,
  receiptIdentity?: Readonly<Record<string, unknown>>
): string {
  const normalizeDiagnostic = (input: unknown): string =>
    typeof input === 'string'
      ? input
          .trim()
          .toLowerCase()
          .replace(/(?:[a-z0-9_.-]+\/)*[a-z0-9_.-]+\.lean(?::\d+(?::\d+)?)?/gu, '<file>')
          .replace(/\bline\s+\d+(?:\s*,\s*column\s+\d+)?\b/gu, 'line <n>')
          .replace(/\s+/gu, ' ')
      : '';
  const normalizePlanFrontier = (input: unknown): Readonly<Record<string, unknown>> | undefined => {
    if (!isRecord(input)) return undefined;
    const nodes = Array.isArray(input.planNodes)
      ? input.planNodes
          .filter(isRecord)
          .map((node) => ({
            id: typeof node.id === 'string' ? node.id : '',
            status: typeof node.status === 'string' ? node.status : '',
            parentNodeId: typeof node.parentNodeId === 'string' ? node.parentNodeId : '',
            dependsOn: Array.isArray(node.dependsOn)
              ? node.dependsOn.filter((item): item is string => typeof item === 'string').sort()
              : [],
          }))
          .sort((left, right) => left.id.localeCompare(right.id))
      : [];
    return {
      rootNodeId: typeof input.rootNodeId === 'string' ? input.rootNodeId : '',
      bottleneckNodeId: typeof input.bottleneckNodeId === 'string' ? input.bottleneckNodeId : '',
      openFrontierNodeIds: Array.isArray(input.openFrontierNodeIds)
        ? input.openFrontierNodeIds.filter((item): item is string => typeof item === 'string').sort()
        : [],
      nodes,
    };
  };
  const finalPlanFrontier = normalizePlanFrontier(value.planAfter);
  const normalizedReceipt = receiptIdentity
    ? {
        receiptId: typeof receiptIdentity.receiptId === 'string' ? receiptIdentity.receiptId : '',
        proofHash: typeof receiptIdentity.proofHash === 'string' ? receiptIdentity.proofHash : '',
        theoremDeclarationHash:
          typeof receiptIdentity.theoremDeclarationHash === 'string' ? receiptIdentity.theoremDeclarationHash : '',
        sourceDeclarationHash:
          typeof receiptIdentity.sourceDeclarationHash === 'string' ? receiptIdentity.sourceDeclarationHash : '',
        planNodeId: typeof receiptIdentity.planNodeId === 'string' ? receiptIdentity.planNodeId : '',
        helperPlanNodeId: typeof receiptIdentity.helperPlanNodeId === 'string' ? receiptIdentity.helperPlanNodeId : '',
      }
    : undefined;
  const normalized = {
    statementHash: typeof value.statementHash === 'string' ? value.statementHash : '',
    routeFingerprint: typeof value.routeFingerprint === 'string' ? value.routeFingerprint : '',
    activePlanNodeId: typeof value.activePlanNodeId === 'string' ? value.activePlanNodeId : '',
    sourceProgress: isRecord(value.sourceProgress)
      ? {
          artifactPath: typeof value.sourceProgress.artifactPath === 'string' ? value.sourceProgress.artifactPath : '',
          changedDeclarationNames: Array.isArray(value.sourceProgress.changedDeclarationNames)
            ? value.sourceProgress.changedDeclarationNames
                .filter((item): item is string => typeof item === 'string')
                .sort()
            : [],
          baseSourceHash:
            typeof value.sourceProgress.baseSourceHash === 'string' ? value.sourceProgress.baseSourceHash : '',
          candidateSourceHash:
            typeof value.sourceProgress.candidateSourceHash === 'string'
              ? value.sourceProgress.candidateSourceHash
              : '',
        }
      : undefined,
    openGoalCountAfter: Number.isSafeInteger(value.openGoalCountAfter) ? value.openGoalCountAfter : 0,
    openGoalFingerprintAfter: typeof value.openGoalFingerprintAfter === 'string' ? value.openGoalFingerprintAfter : '',
    firstLeanErrorAfter: normalizeDiagnostic(value.firstLeanErrorAfter),
    failureCategory: typeof value.failureCategory === 'string' ? value.failureCategory : '',
    reviewAction: typeof value.reviewAction === 'string' ? value.reviewAction : '',
    finalPlanFrontier,
    receipt: normalizedReceipt,
  };
  return crypto.createHash('sha256').update(JSON.stringify(normalized), 'utf8').digest('hex');
}

function deriveMathReceiptFingerprintIdentity(
  receipts: readonly unknown[]
): Readonly<Record<string, unknown>> | undefined {
  const records = receipts.filter(isRecord);
  if (!records.length) return undefined;
  // Receipt arrays are assembled from several optional result fields.  Sort by
  // semantic role and receipt id so a caller cannot change the progress
  // identity merely by reordering that array.
  const ordered = records.toSorted((left, right) => {
    const role = (value: Readonly<Record<string, unknown>>): number =>
      typeof value.helperPlanNodeId === 'string' ? 2 : typeof value.planNodeId === 'string' ? 1 : 0;
    return role(left) - role(right) || String(left.receiptId ?? '').localeCompare(String(right.receiptId ?? ''));
  });
  const primary = ordered[0]!;
  const nodeReceipt = ordered.find((receipt) => typeof receipt.planNodeId === 'string');
  const helperReceipt = ordered.find((receipt) => typeof receipt.helperPlanNodeId === 'string');
  return Object.freeze({
    ...(typeof primary.receiptId === 'string' ? { receiptId: primary.receiptId } : {}),
    ...(typeof primary.proofHash === 'string' ? { proofHash: primary.proofHash } : {}),
    ...(typeof primary.theoremDeclarationHash === 'string'
      ? { theoremDeclarationHash: primary.theoremDeclarationHash }
      : {}),
    ...(typeof primary.sourceDeclarationHash === 'string'
      ? { sourceDeclarationHash: primary.sourceDeclarationHash }
      : {}),
    ...(typeof nodeReceipt?.planNodeId === 'string' ? { planNodeId: nodeReceipt.planNodeId } : {}),
    ...(typeof helperReceipt?.helperPlanNodeId === 'string'
      ? { helperPlanNodeId: helperReceipt.helperPlanNodeId }
      : {}),
  });
}

function deriveMathLeanRuntime(
  assignment: ResearchTeamAssignment,
  result: Record<string, unknown>
): Readonly<{
  disposition: 'accepted' | 'refuted' | 'inconclusive' | 'blocked';
  math: Readonly<Record<string, unknown>>;
}> {
  const supplied = isRecord(result.math) ? result.math : {};
  const directAttempt = assignment.math?.directAttempt === true;
  const {
    wholeProofProbe: _wholeProofProbe,
    verifiedPlanNodeIdsAdded: _verifiedPlanNodeIdsAdded,
    progressFingerprint: _progressFingerprint,
    failureCategory: _failureCategory,
    ...suppliedProgressWithoutIdentity
  } = supplied;
  const suppliedProgress = directAttempt
    ? suppliedProgressWithoutIdentity
    : {
        ...suppliedProgressWithoutIdentity,
        ...(_wholeProofProbe !== undefined ? { wholeProofProbe: _wholeProofProbe } : {}),
        ...(_verifiedPlanNodeIdsAdded !== undefined ? { verifiedPlanNodeIdsAdded: _verifiedPlanNodeIdsAdded } : {}),
      };
  const checkpoint = isRecord(result.mathCheckpoint) ? result.mathCheckpoint : undefined;
  const ledger = checkpoint && isRecord(checkpoint.ledger) ? checkpoint.ledger : checkpoint;
  const failureCategory = typeof ledger?.failureCategory === 'string' ? ledger.failureCategory : '';
  const localGateReceipt = isRecord(result.localGateReceipt) ? result.localGateReceipt : undefined;
  const mathNodeReceipt = isRecord(result.mathNodeReceipt) ? result.mathNodeReceipt : undefined;
  const mathHelperReceipt = isRecord(result.mathHelperReceipt) ? result.mathHelperReceipt : undefined;
  const verifiedMathHelperReceipt =
    mathHelperReceipt && typeof mathHelperReceipt.receiptId === 'string' && mathHelperReceipt.receiptId.trim()
      ? mathHelperReceipt
      : undefined;
  const integer = (value: unknown): number | undefined =>
    Number.isSafeInteger(value) && Number(value) >= 0 ? Number(value) : undefined;
  const hasKernelReceipt = Boolean(localGateReceipt || mathNodeReceipt || verifiedMathHelperReceipt);
  const helperOnlyDirect = directAttempt && Boolean(verifiedMathHelperReceipt) && !localGateReceipt && !mathNodeReceipt;
  const openGoalCountAfterValue = integer(supplied.openGoalCountAfter) ?? 0;
  const openGoalCountAfter = helperOnlyDirect ? Math.max(1, openGoalCountAfterValue) : openGoalCountAfterValue;
  const openGoalCountBeforeValue = integer(supplied.openGoalCountBefore) ?? (hasKernelReceipt ? 1 : openGoalCountAfter);
  const openGoalCountBefore = helperOnlyDirect ? Math.max(1, openGoalCountBeforeValue) : openGoalCountBeforeValue;
  const receiptNodeId =
    typeof mathNodeReceipt?.planNodeId === 'string'
      ? mathNodeReceipt.planNodeId
      : localGateReceipt && !assignment.math?.directAttempt
        ? activeMathRouteCard(assignment)?.rootNodeId
        : undefined;
  const verifiedPlanNodeIdsAdded =
    helperOnlyDirect && typeof verifiedMathHelperReceipt?.helperPlanNodeId === 'string'
      ? Object.freeze([verifiedMathHelperReceipt.helperPlanNodeId])
      : !directAttempt && Array.isArray(supplied.verifiedPlanNodeIdsAdded)
        ? supplied.verifiedPlanNodeIdsAdded
        : !directAttempt && receiptNodeId
          ? Object.freeze([receiptNodeId])
          : !directAttempt && typeof verifiedMathHelperReceipt?.helperPlanNodeId === 'string'
            ? Object.freeze([verifiedMathHelperReceipt.helperPlanNodeId])
            : undefined;
  const suppliedInfraStatus =
    supplied.infraStatus === 'ok'
      ? 'ready'
      : typeof supplied.infraStatus === 'string' &&
          MATH_INFRA_STATUSES.includes(supplied.infraStatus as (typeof MATH_INFRA_STATUSES)[number])
        ? supplied.infraStatus
        : undefined;
  const infraStatus =
    suppliedInfraStatus ??
    (failureCategory === 'infra' || failureCategory === 'toolchain' ? 'tool_unavailable' : 'ready');
  const activePlanNodeId = assignment.math?.activePlanNodeId;
  const wholeProblemDirectAttempt = !activePlanNodeId || activePlanNodeId === 'direct-goal';
  const solverDeclaredComplete =
    directAttempt &&
    wholeProblemDirectAttempt &&
    !hasKernelReceipt &&
    infraStatus === 'ready' &&
    supplied.routeDisposition === 'advance' &&
    openGoalCountBefore > 0 &&
    openGoalCountAfter === 0 &&
    isRecord(result.git) &&
    typeof result.git.headCommit === 'string' &&
    Boolean(result.git.headCommit.trim()) &&
    // A solver declaration without a durable Kernel receipt is only useful
    // when the Worker actually delivered a new commit.  An unchanged base
    // can still contain `sorry` (or simply be a stale transcript), so it must
    // remain a repair episode until the external evaluator sees a real delta.
    result.git.headCommit !== assignment.git.baseCommit;
  const declarationClusterDeclaredComplete =
    directAttempt &&
    !wholeProblemDirectAttempt &&
    assignment.math?.stage === 'formalize' &&
    infraStatus === 'ready' &&
    supplied.routeDisposition === 'advance' &&
    openGoalCountBefore > 0 &&
    openGoalCountAfter === 0 &&
    isRecord(result.git) &&
    typeof result.git.headCommit === 'string' &&
    Boolean(result.git.headCommit.trim()) &&
    result.git.headCommit !== assignment.git.baseCommit;
  const madeProgress =
    hasKernelReceipt || openGoalCountAfter < openGoalCountBefore || Boolean(verifiedPlanNodeIdsAdded?.length);
  const suppliedRouteDisposition =
    typeof supplied.routeDisposition === 'string' &&
    MATH_ROUTE_DISPOSITIONS.includes(supplied.routeDisposition as (typeof MATH_ROUTE_DISPOSITIONS)[number])
      ? supplied.routeDisposition
      : undefined;
  const routeDisposition =
    failureCategory === 'wrong_statement' || failureCategory === 'counterexample'
      ? 'reject'
      : failureCategory === 'duplicate_route'
        ? 'duplicate'
        : helperOnlyDirect
          ? 'blocked'
          : hasKernelReceipt || solverDeclaredComplete || declarationClusterDeclaredComplete
            ? 'advance'
            : suppliedRouteDisposition === 'reject' || suppliedRouteDisposition === 'duplicate'
              ? suppliedRouteDisposition
              : 'blocked';
  const checkpointObjective =
    typeof ledger?.nextSingleObjective === 'string'
      ? ledger.nextSingleObjective
      : typeof checkpoint?.nextSingleObjective === 'string'
        ? checkpoint.nextSingleObjective
        : undefined;
  const nextSingleObjective =
    typeof supplied.nextSingleObjective === 'string'
      ? supplied.nextSingleObjective
      : (checkpointObjective ??
        (solverDeclaredComplete
          ? 'Integrate the unchanged solver-complete commit and submit it to the external evaluator.'
          : declarationClusterDeclaredComplete
            ? 'Integrate this completed declaration cluster and continue with the next open proof node.'
            : localGateReceipt
              ? 'Send the unchanged kernel-verified candidate to independent review.'
              : mathNodeReceipt
                ? 'Continue from the next open proof obligation.'
                : verifiedMathHelperReceipt
                  ? 'Promote the verified helper and continue the same whole-problem proof episode.'
                  : infraStatus !== 'ready'
                    ? 'Retry the same proof step after restoring the Lean toolchain.'
                    : 'Repair the first remaining Lean error on the same candidate.'));
  const receipt = localGateReceipt ?? mathNodeReceipt ?? verifiedMathHelperReceipt;
  const suppliedEvidenceDelta = Array.isArray(supplied.evidenceDelta)
    ? supplied.evidenceDelta.filter(
        (item): item is Record<string, unknown> =>
          isRecord(item) &&
          typeof item.kind === 'string' &&
          MATH_EVIDENCE_DELTA_KINDS.includes(item.kind as (typeof MATH_EVIDENCE_DELTA_KINDS)[number]) &&
          // Counterexample probe evidence is injected by the host after the
          // Worker payload is hydrated; a Worker cannot self-report it.
          item.kind !== 'counterexample_probe' &&
          (!['kernel_declaration', 'helper_declaration'].includes(item.kind) || hasKernelReceipt) &&
          typeof item.ref === 'string' &&
          Boolean(item.ref.trim()) &&
          typeof item.summary === 'string' &&
          Boolean(item.summary.trim())
      )
    : [];
  const evidenceDelta = suppliedEvidenceDelta.length
    ? Object.freeze(suppliedEvidenceDelta)
    : receipt && typeof receipt.receiptId === 'string'
      ? Object.freeze([
          Object.freeze({
            kind: verifiedMathHelperReceipt ? 'helper_declaration' : 'kernel_declaration',
            ref: `lean-receipt:${receipt.receiptId}`,
            summary: localGateReceipt
              ? 'The whole candidate was accepted by the Lean kernel.'
              : verifiedMathHelperReceipt
                ? 'An expanded infrastructure helper was accepted by the Lean kernel.'
                : 'The active proof node was accepted by the Lean kernel.',
          }),
        ])
      : Object.freeze([]);
  const provesNegation =
    localGateReceipt?.claim === 'negation' || assignment.math?.fastCheck?.candidateClaim === 'negation';
  const disposition = helperOnlyDirect
    ? ('accepted' as const)
    : hasKernelReceipt || solverDeclaredComplete || declarationClusterDeclaredComplete
      ? provesNegation
        ? ('refuted' as const)
        : ('accepted' as const)
      : failureCategory === 'wrong_statement' || failureCategory === 'counterexample'
        ? ('refuted' as const)
        : infraStatus !== 'ready'
          ? ('blocked' as const)
          : madeProgress
            ? ('accepted' as const)
            : ('inconclusive' as const);

  const math = {
    checkedDeclarationsAdded: integer(supplied.checkedDeclarationsAdded) ?? (hasKernelReceipt ? 1 : 0),
    openGoalCountBefore,
    openGoalCountAfter,
    ...suppliedProgress,
    ...(helperOnlyDirect
      ? {
          checkedDeclarationsAdded: Math.max(1, integer(supplied.checkedDeclarationsAdded) ?? 0),
          openGoalCountBefore,
          openGoalCountAfter,
        }
      : {}),
    evidenceDelta,
    ...(verifiedPlanNodeIdsAdded ? { verifiedPlanNodeIdsAdded } : {}),
    ...(failureCategory && MATH_FAILURE_CATEGORIES.includes(failureCategory as MathFailureCategory)
      ? { failureCategory: failureCategory as MathFailureCategory }
      : {}),
    routeDisposition,
    nextSingleObjective,
    infraStatus,
  };
  const receiptIdentity = deriveMathReceiptFingerprintIdentity([
    localGateReceipt,
    mathNodeReceipt,
    verifiedMathHelperReceipt,
  ]);

  return Object.freeze({
    disposition,
    math: Object.freeze({
      ...math,
      progressFingerprint: deriveMathProgressFingerprint(math, receiptIdentity),
    }),
  });
}

function hydrateMathRouteCard(
  assignment: ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  routeCard: Record<string, unknown>
): Readonly<Record<string, unknown>> {
  const planNodes = Array.isArray(routeCard.planNodes)
    ? (routeCard.planNodes as unknown as readonly MathPlanNode[])
    : undefined;
  const schedule = planNodes ? mathActionablePlanSchedule(planNodes) : undefined;
  const rootNodeId = schedule?.rootNodeId;
  const openFrontierNodeIds = schedule?.openFrontierNodeIds;
  const bottleneckNodeId = schedule?.rankedNodeIds[0];
  return Object.freeze({
    statementHash: assignment.math?.statementHash,
    routeFingerprint: assignment.math?.routeFingerprint,
    ...(rootNodeId ? { rootNodeId } : {}),
    ...(bottleneckNodeId ? { bottleneckNodeId } : {}),
    ...(openFrontierNodeIds ? { openFrontierNodeIds } : {}),
    ...routeCard,
    proposerSessionId: `${capability.teamId}:${target.slotId}:${assignment.assignmentId}`,
  });
}

function deriveMathRouteRuntime(
  assignment: ResearchTeamAssignment,
  routeCard: Record<string, unknown>
): Readonly<{
  disposition: 'accepted';
  math: Readonly<Record<string, unknown>>;
}> {
  const premiseBundle = isRecord(routeCard.premiseBundle) ? routeCard.premiseBundle : undefined;
  let checkedDeclarationsAdded = 0;
  const evidenceDelta: Readonly<Record<string, unknown>>[] = [];
  for (const premise of Array.isArray(premiseBundle?.premises) ? premiseBundle.premises : []) {
    if (!isRecord(premise) || premise.status !== 'typed') continue;
    checkedDeclarationsAdded += 1;
    evidenceDelta.push(
      Object.freeze({
        kind: premise.sourceKind === 'verified_local' ? 'kernel_declaration' : 'mathlib_declaration',
        ref: String(premise.declarationName ?? ''),
        summary: String(premise.intendedUse ?? ''),
      })
    );
  }
  return Object.freeze({
    disposition: 'accepted',
    math: createMathRuntimeProgress(assignment, {
      checkedDeclarationsAdded,
      evidenceDelta,
      routeDisposition: 'advance',
      nextSingleObjective:
        assignment.math?.routeProposalMode === 'candidate'
          ? 'Have the Lead compare this probed candidate and promote only the strongest surviving route.'
          : 'Have the Lead compare and probe this route against the route slate.',
    }),
  });
}

function hydrateMathExplorerProgress(progress: Record<string, unknown>): Readonly<Record<string, unknown>> {
  return Object.freeze({
    checkedDeclarationsAdded: 0,
    openGoalCountBefore: 0,
    openGoalCountAfter: 0,
    evidenceDelta: Object.freeze([]),
    ...progress,
  });
}

function hydrateMathCheckpoint(
  assignment: ResearchTeamAssignment,
  math: Record<string, unknown>,
  checkpoint: Record<string, unknown>,
  defaultTargetCommit = assignment.git.baseCommit
): Readonly<Record<string, unknown>> {
  const ledgerInput = isRecord(checkpoint.ledger) ? checkpoint.ledger : checkpoint;
  const priorTriedRoutes = assignment.math?.failureLedger?.triedRoutes;
  const priorStructureSignatures = assignment.math?.failureLedger?.triedRouteStructureSignatures;
  const currentCard = activeMathRouteCard(assignment);
  const currentStructureSignature = currentCard ? mathRouteStructureSignatureFromNormalized(currentCard) : undefined;
  const triedRouteStructureSignatures: string[] = [];
  const seenStructureSignatures = new Set<string>();
  for (const signature of priorStructureSignatures ?? []) {
    if (seenStructureSignatures.has(signature)) continue;
    seenStructureSignatures.add(signature);
    triedRouteStructureSignatures.push(signature);
  }
  if (currentStructureSignature && !seenStructureSignatures.has(currentStructureSignature)) {
    triedRouteStructureSignatures.push(currentStructureSignature);
  }
  return Object.freeze({
    checkpointId:
      typeof checkpoint.checkpointId === 'string'
        ? checkpoint.checkpointId
        : `${assignment.math?.stage}-${assignment.assignmentId}`,
    targetCommit: checkpoint.targetCommit ?? defaultTargetCommit,
    updatedAt: typeof checkpoint.updatedAt === 'number' ? checkpoint.updatedAt : Date.now(),
    ledger: Object.freeze({
      stage: assignment.math?.stage,
      statementHash: assignment.math?.statementHash,
      activeRoute: assignment.math?.routeFingerprint,
      triedRoutes: priorTriedRoutes ?? Object.freeze([assignment.math?.routeFingerprint]),
      triedRouteStructureSignatures: Object.freeze(triedRouteStructureSignatures),
      ...(typeof math.progressFingerprint === 'string'
        ? { progressFingerprint: math.progressFingerprint }
        : typeof ledgerInput.progressFingerprint === 'string'
          ? { progressFingerprint: ledgerInput.progressFingerprint }
          : {}),
      nextSingleObjective: math.nextSingleObjective,
      doNotRepeatRefs: Object.freeze([]),
      ...ledgerInput,
    }),
  });
}

function deriveMathReviewRuntime(
  assignment: ResearchTeamAssignment,
  receipt: MathLocalGateReceipt,
  review: Record<string, unknown>
): Readonly<{
  disposition: 'accepted' | 'inconclusive';
  math: Readonly<Record<string, unknown>>;
  mathCheckpoint?: Readonly<Record<string, unknown>>;
}> {
  const sound = review.verdict === 'sound';
  const reviewAction = mathCandidateReviewAction({
    verdict: review.verdict as 'sound' | 'gap' | 'wrong',
  });
  const repairTarget = typeof review.repairTarget === 'string' ? review.repairTarget.trim() : '';
  const firstFault = typeof review.firstFault === 'string' ? review.firstFault.trim() : '';
  const findings = Array.isArray(review.findings)
    ? review.findings.filter(
        (finding): finding is Record<string, unknown> =>
          isRecord(finding) && typeof finding.message === 'string' && Array.isArray(finding.evidenceRefs)
      )
    : [];
  const materialFinding = findings.find((finding) => finding.severity === 'blocker' || finding.severity === 'major');
  const findingRepairTarget =
    materialFinding && typeof materialFinding.repairTarget === 'string' ? materialFinding.repairTarget.trim() : '';
  const findingMessage =
    materialFinding && typeof materialFinding.message === 'string' ? materialFinding.message.trim() : '';
  const nextSingleObjective = sound
    ? 'Run official verification on the unchanged reviewed commit.'
    : reviewAction === 'reject'
      ? `Abandon the reviewed route and select a structurally distinct route: ${firstFault || findingMessage || 'the reviewer found a structural counterexample.'}`
      : findingRepairTarget ||
        repairTarget ||
        (firstFault ? `Resolve review finding: ${firstFault}` : 'Repair the reviewed candidate.');
  const math = createMathRuntimeProgress(assignment, {
    evidenceDelta: [
      Object.freeze({
        kind: 'kernel_declaration',
        ref: `local-gate:${receipt.receiptId}`,
        summary: 'Reviewed the frozen Lean kernel receipt.',
      }),
      ...findings.slice(0, 4).map((finding) =>
        Object.freeze({
          kind: typeof finding.kind === 'string' ? finding.kind : 'proof_gap',
          ref: String((finding.evidenceRefs as unknown[])[0] ?? `review:${receipt.receiptId}`),
          summary: String(finding.message),
        })
      ),
    ],
    routeDisposition: sound ? 'advance' : 'reject',
    reviewAction,
    nextSingleObjective,
  });
  return Object.freeze({
    disposition: sound ? 'accepted' : 'inconclusive',
    math,
    ...(!sound
      ? {
          mathCheckpoint: Object.freeze({
            checkpointId: `review-${assignment.assignmentId}`,
            targetCommit: receipt.targetCommit,
            updatedAt: Date.now(),
            ledger: Object.freeze({
              stage: 'review',
              statementHash: assignment.math?.statementHash,
              activeRoute: assignment.math?.routeFingerprint,
              triedRoutes: Object.freeze([assignment.math?.routeFingerprint]),
              nextSingleObjective,
              failureCategory: 'review_gap',
              doNotRepeatRefs: Object.freeze([]),
            }),
          }),
        }
      : {}),
  });
}

function assignmentMathPlanSnapshot(
  assignment: ResearchTeamAssignment,
  progress?: Readonly<Record<string, unknown>>
): MathPlanSnapshot | undefined {
  if (assignment.math?.stage !== 'formalize') return undefined;
  const routeCard = activeMathRouteCard(assignment);
  if (!routeCard) {
    // Direct assignments deliberately omit routed DAG state from the Worker
    // projection. A helper expansion still needs a runtime-owned parent plan so
    // its receipt can be bound to `direct-goal` without making the helper the
    // whole-problem theorem.
    if (assignment.math.directAttempt !== true || !progress || !isRecord(progress.planExpansion)) {
      return undefined;
    }
    const problemContract = assignment.math.problemContract;
    const rootStatement =
      assignment.math.fastCheck?.candidateClaim === 'negation'
        ? problemContract?.formalNegationStatement
        : problemContract?.formalStatement;
    const rootNode: MathPlanNode = Object.freeze({
      id: 'direct-goal',
      informalClaim: problemContract?.informalStatement ?? assignment.objective,
      provisionalLeanStatement: rootStatement ?? assignment.objective,
      dependsOn: Object.freeze([]),
      role: 'goal',
      kind: 'theorem',
      status: 'proposed',
      evidenceRefs: Object.freeze([]),
    });
    return Object.freeze({
      rootNodeId: rootNode.id,
      planNodes: Object.freeze([rootNode]),
      bottleneckNodeId: rootNode.id,
      openFrontierNodeIds: Object.freeze([rootNode.id]),
    });
  }
  return Object.freeze({
    rootNodeId: routeCard.rootNodeId,
    planNodes: routeCard.planNodes,
    ...(routeCard.bottleneckNodeId ? { bottleneckNodeId: routeCard.bottleneckNodeId } : {}),
    openFrontierNodeIds: routeCard.openFrontierNodeIds,
  });
}

function applyMathPlanVerificationDelta(
  planBefore: MathPlanSnapshot,
  math: Record<string, unknown>,
  result: Record<string, unknown>,
  proofState?: MathProofState
): MathPlanSnapshot {
  const expansion = isRecord(math.planExpansion) ? normalizeMathPlanExpansion(math.planExpansion as never) : undefined;
  const verifiedNodeIds = new Set<string>();
  for (const nodeId of Array.isArray(math.verifiedPlanNodeIdsAdded) ? math.verifiedPlanNodeIdsAdded : []) {
    if (typeof nodeId === 'string') verifiedNodeIds.add(nodeId);
  }
  if (
    isRecord(result.mathHelperReceipt) &&
    typeof result.mathHelperReceipt.helperPlanNodeId === 'string' &&
    typeof result.mathHelperReceipt.receiptId === 'string' &&
    result.mathHelperReceipt.receiptId.trim().length > 0
  ) {
    verifiedNodeIds.add(result.mathHelperReceipt.helperPlanNodeId);
  }
  const receiptRefs: string[] = [];
  for (const value of [result.mathNodeReceipt, result.mathHelperReceipt, result.localGateReceipt]) {
    if (!isRecord(value) || typeof value.receiptId !== 'string' || value.receiptId.trim().length === 0) continue;
    receiptRefs.push(value.receiptId);
  }
  const planNodes = Object.freeze(
    [...planBefore.planNodes, ...(expansion?.addedNodes ?? [])].map((node) => {
      if (!verifiedNodeIds.has(node.id) || node.status === 'kernel_verified') return node;
      const evidenceRefs: string[] = [];
      const seenEvidenceRefs = new Set<string>();
      for (const evidenceRef of node.evidenceRefs) {
        if (seenEvidenceRefs.has(evidenceRef)) continue;
        seenEvidenceRefs.add(evidenceRef);
        evidenceRefs.push(evidenceRef);
      }
      for (const evidenceRef of receiptRefs) {
        if (seenEvidenceRefs.has(evidenceRef)) continue;
        seenEvidenceRefs.add(evidenceRef);
        evidenceRefs.push(evidenceRef);
      }
      return Object.freeze({
        ...node,
        status: 'kernel_verified' as const,
        evidenceRefs: Object.freeze(evidenceRefs),
      });
    })
  );
  const schedule = mathActionablePlanScheduleFromNormalized(planNodes);
  const frontier = deriveLeanProofFrontier({
    plan: Object.freeze({
      rootNodeId: planBefore.rootNodeId,
      planNodes,
      openFrontierNodeIds: schedule.openFrontierNodeIds,
      ...(schedule.rankedNodeIds[0] ? { bottleneckNodeId: schedule.rankedNodeIds[0] } : {}),
    }),
    verifiedNodeIds: [...verifiedNodeIds],
    ...(proofState ? { proofState } : {}),
  });
  return Object.freeze({
    rootNodeId: planBefore.rootNodeId,
    planNodes,
    ...(frontier.bottleneckNodeId ? { bottleneckNodeId: frontier.bottleneckNodeId } : {}),
    openFrontierNodeIds: frontier.openNodeIds,
  });
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}
