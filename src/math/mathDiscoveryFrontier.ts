import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import {
  assertCheckedMathProofBlock,
  buildMathProofBlockCandidates,
  planMathProofBlockInsertion,
  type CheckedMathProofBlock,
  type MathProofBlockRequest,
} from "./mathProofBlocks";
import { generateLeanProofActionCandidates, type LeanProofActionCandidate } from "./leanProofActionSearch";
import { runLeanEvalLeanProbe } from "./leanEvalLeanProbe";
import { assertMathCanonicalPath } from "./mathRunBinding";
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";

export type MathDiscoveryObstruction = Readonly<{
  connectionId: string;
  connectionName: string;
  sourceHash: string;
  declarationHash: string;
  premiseIndex: number;
  contextFingerprint: string;
  checkedSourceIds: readonly string[];
  authority: 'kernel_checked_negated_premise';
}>;

/** Rebuilds negative support from actual Lean expressions. A condition is rejected
 * only when its negation closes universally, without using *any* proposition
 * assumption from the connection telescope. No target or source is rewritten. */
export async function inspectMathDiscoveryObstructions(
  input: Pick<MathProofBlockRequest, 'projectRoot' | 'proofPath' | 'deadlineAt' | 'signal' | 'env'> & {
    sourceHash: string;
  },
  blocks: readonly CheckedMathProofBlock[]
): Promise<
  Readonly<{
    unsupportedConnectionIds: readonly string[];
    observations: readonly MathDiscoveryObstruction[];
    reason?: string;
  }>
> {
  const unknown = (reason: string) => ({
    unsupportedConnectionIds: [] as string[],
    observations: [] as MathDiscoveryObstruction[],
    reason,
  });
  input.signal?.throwIfAborted();
  if (Date.now() >= input.deadlineAt) return unknown('negative premise deadline elapsed');
  if (
    path.isAbsolute(input.proofPath) ||
    input.proofPath.split(/[\\/]/u).some((part) => !part || part === '.' || part === '..') ||
    !isAllowedMathProofSource(input.proofPath)
  )
    throw new Error('math_discovery_invalid_proof_path');
  assertMathCanonicalPath(input.projectRoot);
  assertMathCanonicalPath(path.join(input.projectRoot, input.proofPath));
  if (blocks.length < 2 || blocks.length > 8) return unknown('outside bounded connection scope');
  for (const block of blocks) assertCheckedMathProofBlock(block);
  const scope = blocks[0]!.scope;
  if (blocks.some((block) => block.scope.runId !== scope.runId || block.scope.environmentId !== scope.environmentId))
    return unknown('mixed connection environment');
  const original = fs.readFileSync(path.join(input.projectRoot, input.proofPath), 'utf8');
  const hash = (text: string) => crypto.createHash('sha256').update(text).digest('hex');
  if (hash(original) !== input.sourceHash) throw new Error('math_discovery_source_changed');
  const selected = [...new Map(blocks.map((block) => [block.id, block])).values()];
  if (
    new Set(selected.map((block) => block.sourceHash)).size > 3 ||
    selected.some((block) => !/^[A-Za-z_][A-Za-z0-9_'.]*$/u.test(block.declarationName))
  )
    return unknown('outside bounded frozen source scope');
  // Assemble the actual checked source union using the same conflict/command
  // rules as consumption; import Lean belongs only to this isolated host check.
  const base = selected[0]!.source;
  const insertion = planMathProofBlockInsertion({ source: base, premises: [] }, selected);
  if (!insertion) return unknown('frozen source declarations cannot be safely combined');
  const combined = base.slice(0, insertion.offset) + insertion.text + base.slice(insertion.offset);
  const token = crypto.randomBytes(16).toString('hex');
  const marker = `DS_DISCOVERY_OBSTRUCTION_${token}:`;
  const names = selected.map((block) => block.declarationName);
  const tactic = `solve_by_elim (maxDepth := 4) only [${names.join(', ')}]`;
  const checks = selected
    .map(
      (block, index) => `
    let declaration ← Lean.getConstInfo (${JSON.stringify(block.declarationName)}.toName)
    Lean.Meta.forallTelescopeReducing declaration.type fun parameters conclusion => do
      if conclusion.isConstOf (Lean.Name.mkSimple "False") then return
      let mut universals : Array Lean.Expr := #[]
      for parameterIndex in [:parameters.size] do
        let parameter := parameters[parameterIndex]!
        let premise ← Lean.Meta.inferType parameter
        if !(← Lean.Meta.isProp premise) then
          universals := universals.push parameter
        else
          let saved ← Lean.Elab.Tactic.saveState
          try
            let negative ← Lean.Meta.mkAppM (Lean.Name.mkSimple "Not") #[premise]
            let goal ← Lean.Meta.mkFreshExprMVar negative
            Lean.Elab.Tactic.setGoals [goal.mvarId!]
            let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) (Lean.Name.mkSimple "tactic") ${JSON.stringify(tactic)} with
              | .ok stx => pure stx
              | .error message => throwError "{message}"
            Lean.Elab.Tactic.evalTactic stx
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let proof ← Lean.instantiateMVars goal
            if proof.hasMVar || proof.hasSorry then throwError "open negative premise"
            let closed ← Lean.Meta.mkLambdaFVars universals proof
            let expected ← Lean.Meta.mkForallFVars universals negative
            if closed.hasFVar || closed.hasMVar || expected.hasFVar || expected.hasMVar then throwError "negative premise depends on unsatisfied conditions"
            Lean.Meta.checkWithKernel closed
            unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType closed) expected do throwError "negative premise type drift"
            let index := parameterIndex
            saved.restore
            Lean.logInfo m!"${marker}${index}:{index}"
          catch _ => saved.restore`
    )
    .join('\n');
  const theoremName = `discovery_obstruction_check_${token}`;
  const source = `import Lean\n${combined}\ntheorem ${theoremName} : True := by\n  run_tac do${checks}\n  trivial\n`;
  const checked = await runLeanEvalLeanProbe({
    workspaceRoot: input.projectRoot,
    sourceFile: input.proofPath,
    sourceText: source,
    mode: 'compile',
    prepareLocalDependencies: true,
    timeoutMs: Math.max(1, input.deadlineAt - Date.now()),
    signal: input.signal,
    env: input.env,
  });
  input.signal?.throwIfAborted();
  if (hash(fs.readFileSync(path.join(input.projectRoot, input.proofPath), 'utf8')) !== input.sourceHash)
    throw new Error('math_discovery_source_changed');
  if (Date.now() >= input.deadlineAt) return unknown('negative premise deadline elapsed');
  if (checked.status !== 'passed' || checked.executionDisposition !== 'completed')
    return unknown(checked.error ?? checked.diagnostics ?? 'negative premise check unavailable');
  const logs = [checked.diagnostics];
  const observations: MathDiscoveryObstruction[] = [];
  for (const message of logs)
    for (const match of message.matchAll(new RegExp(`${marker}(\\d+):(\\d+)`, 'gu'))) {
      const connection = selected[Number(match[1])];
      if (!connection) continue;
      const premiseIndex = Number(match[2]);
      observations.push(
        Object.freeze({
          connectionId: connection.id,
          connectionName: connection.declarationName,
          sourceHash: connection.sourceHash,
          declarationHash: connection.declarationHash,
          premiseIndex,
          contextFingerprint: hash(
            JSON.stringify([
              input.sourceHash,
              checked.proofStateFingerprint,
              checked.environmentFingerprint,
              connection.id,
              premiseIndex,
            ])
          ),
          checkedSourceIds: Object.freeze(selected.map((block) => block.id)),
          authority: 'kernel_checked_negated_premise',
        })
      );
    }
  return Object.freeze({
    unsupportedConnectionIds: Object.freeze([...new Set(observations.map((observation) => observation.connectionId))]),
    observations: Object.freeze(observations),
  });
}

/** Reconstructed from currently authorized, actually checked sources. No persisted
 * `proved` flags, goal-string unification, or independent existential witnesses.
 * Lean performs AND premise solving and OR backtracking in one proof state. */
export function buildMathDiscoveryCandidates(
  input: Parameters<typeof buildMathProofBlockCandidates>[0],
  blocks: readonly CheckedMathProofBlock[]
): readonly LeanProofActionCandidate[] {
  const direct = buildMathProofBlockCandidates(input, blocks);
  if (blocks.length < 2) return direct;
  for (const block of blocks) assertCheckedMathProofBlock(block);
  const scope = blocks[0]!.scope;
  if (blocks.some((block) => block.scope.runId !== scope.runId || block.scope.environmentId !== scope.environmentId))
    return direct;
  // A conflicting, unrelated finding must not veto a usable connection. Keep
  // the existing eight-block/three-source scope and grow one compatible group
  // per seed; this is bounded greedy assembly, not all-subset search.
  const selected = [...new Map(blocks.map((block) => [block.id, block])).values()]
    .slice(0, 8)
    .filter(
      (block) =>
        /^[A-Za-z_][A-Za-z0-9_'.]*$/u.test(block.declarationName) && !!planMathProofBlockInsertion(input, [block])
    );
  const candidates = [...direct];
  const seen = new Set<string>();
  for (const seed of selected) {
    let group = [seed];
    for (const block of selected) {
      if (block.id === seed.id) continue;
      const proposal = [...group, block];
      if (new Set(proposal.map((item) => item.sourceHash)).size <= 3 && planMathProofBlockInsertion(input, proposal))
        group = proposal;
    }
    // Canonical ordering deduplicates groups reached from different seeds and
    // preserves the original candidate when the complete set is compatible.
    const included = new Set(group.map((block) => block.id));
    group = selected.filter((block) => included.has(block.id));
    const key = JSON.stringify(group.map((block) => block.id));
    if (seen.has(key)) continue;
    seen.add(key);
    const names = [...new Set(group.map((block) => block.declarationName))];
    if (names.length < 2) continue;
    const insertion = planMathProofBlockInsertion(input, group);
    if (!insertion) continue;
    // Keep the composed proposal within the existing exact-proof action contract:
    // Lean must close the complete instance before any adoption or work contraction.
    const tactics = [`exact (by solve_by_elim (maxDepth := 4) only [${names.join(', ')}])`];
    // Independent equalities can jointly close a compound goal even when no
    // single conclusion applies. Checked conditional rules still need their
    // premises, and only a completely verified proof can be consumed.
    if (group.some((block) => /[=↔]/u.test(block.elaboratedDeclaration)))
      tactics.push(`exact (by simp_all only [${names.join(', ')}])`);
    for (const tactic of tactics) {
      const generated = generateLeanProofActionCandidates({ ...input, preferredTactic: tactic }).find(
        (candidate) => candidate.payload === tactic
      );
      if (!generated) continue;
      const source =
        generated.source.slice(0, insertion.offset) + insertion.text + generated.source.slice(insertion.offset);
      const candidateId = crypto
        .createHash('sha256')
        .update(JSON.stringify([input.source, group.map((block) => block.id), tactic]))
        .digest('hex');
      candidates.push(Object.freeze({ ...generated, source, candidateId, helperProduced: true }));
    }
  }
  return Object.freeze(candidates);
}
