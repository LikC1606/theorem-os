import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions } from '../math/leanSource';
import { isSimpleLeanName } from '../math/leanSyntax';
import { commitSolverProjection, git, withSolverWorktree, type SolverProblem } from './problem';
import { checkProjectedDeclaration, type ProofCheck } from './modules/evidence';
import { readMathResponse } from './deliveries';
import { hasDeterministicLeanFailure, proofReuseEnvironment } from './proofReuse';

export type LemmaPlan = Readonly<{ proofPath: string; target: string; lemma: string; type: string }>;
export type LemmaEvidence = ProofCheck & Readonly<{
  obligation: 'bridge' | 'lemma';
  sourceCommit: string;
  planDigest: string;
  projectionDigest: string;
  unchangedFailures: number;
  reused: boolean;
}>;
export type LemmaResearch = { plan?: LemmaPlan; error?: string; bridge?: LemmaEvidence; lemma?: LemmaEvidence };

// Archive records cannot authorize reuse: only receipts checked in this process can.
const checkedProjections = new WeakMap<LemmaEvidence, {
  environmentDigest?: string; projectionDigest: string; reusable: boolean; receiptDigest: string;
}>();

/** Proposals in RESEARCH.md are instructions, never mathematical evidence. */
export function readLemmaPlan(task: SolverProblem, worktree: string): LemmaPlan {
  const plan = readMathResponse(worktree, 'math-lemma') as LemmaPlan;
  if (!plan || typeof plan.type !== 'string' || !plan.type.trim() ||
      !isSimpleLeanName(plan.lemma) ||
      !task.targets.some(target => target.proofPath === plan.proofPath && target.theoremName === plan.target))
    throw new Error('math_lemma_plan_invalid');
  return { proofPath: plan.proofPath, target: plan.target, lemma: plan.lemma, type: plan.type };
}

/** Check conditional connection and lemma separately, without relaxing the strict verifier. */
export async function checkLemmaResearch(task: SolverProblem, worktree: string, env: NodeJS.ProcessEnv,
  signal: AbortSignal, source: ProofCheck, plan: LemmaPlan, previous?: LemmaResearch): Promise<LemmaResearch> {
  const sourceFile = fs.readFileSync(path.join(worktree, task.projectRelative, plan.proofPath), 'utf8');
  const regions = inspectLeanDeclarationRegions(sourceFile);
  const local = (name: string) => name.split('.').at(-1)!;
  const helpers = regions.filter(region => local(region.name) === local(plan.lemma));
  if (helpers.length !== 1 || !/^(?:theorem|lemma)\s/u.test(sourceFile.slice(helpers[0]!.startOffset, helpers[0]!.bodyOffset)) ||
      Object.values(task.declarations).some(declarations => declarations.some(item => local(item.name) === local(plan.lemma))))
    return { plan, error: 'math_lemma_requires_new_unambiguous_theorem' };
  const helper = helpers[0]!;
  const target = task.targets.find(item => item.proofPath === plan.proofPath && item.theoremName === plan.target)!;
  const selected = regions.find(region => local(region.name) === local(plan.target));
  if (!selected || helper.startOffset >= selected.startOffset)
    return { plan, error: 'math_lemma_must_precede_target' };
  // Conservative declaration regions are suitable only for ordinary := theorem bodies.
  if (sourceFile.slice(helper.bodyOffset - 2, helper.bodyOffset) !== ':=' ||
      sourceFile.slice(selected.bodyOffset - 2, selected.bodyOffset) !== ':=')
    return { plan, error: 'math_lemma_requires_assignment_proofs' };
  const planDigest = mathDigest(canonicalMathJson({ plan, declarationHash: hashMathFormalSourceDeclaration(sourceFile, plan.lemma),
    targetHash: target.declarationHash, problemReceiptDigest: task.receiptDigest }));
  const check = async (obligation: 'bridge' | 'lemma'): Promise<LemmaEvidence> => {
    signal.throwIfAborted();
    return withSolverWorktree(worktree, source.commit, async checkout => {
      const project = path.join(checkout, task.projectRelative);
      for (const file of task.ownedFiles.filter(file => file.endsWith('.lean'))) {
        const absolute = path.join(project, file);
        let text = fs.readFileSync(absolute, 'utf8');
        const originalNames = new Set(task.declarations[file]!.map(item => item.name));
        for (const region of inspectLeanDeclarationRegions(text).reverse()) {
          const isTarget = file === plan.proofPath && local(region.name) === local(plan.target);
          const isHelper = file === plan.proofPath && local(region.name) === local(plan.lemma);
          if (obligation === 'bridge' && isTarget) {
            const header = text.slice(region.startOffset, region.bodyOffset - 2);
            const match = /^(?:theorem|lemma)\s+[^\s(\[{:]+/u.exec(header);
            if (!match) throw new Error('math_lemma_target_header_unsupported');
            const conditional = `${match[0]} (${local(plan.lemma)} : ${plan.type})${header.slice(match[0].length)}`;
            text = text.slice(0, region.startOffset) + conditional + text.slice(region.bodyOffset - 2);
          } else if ((originalNames.has(region.name) && /^(?:theorem|lemma)\s/u.test(text.slice(region.startOffset, region.bodyOffset))) ||
              (obligation === 'bridge' && isHelper)) {
            text = text.slice(0, region.startOffset) + text.slice(region.endOffset);
          }
        }
        fs.writeFileSync(absolute, text);
      }
      const commit = commitSolverProjection(task, checkout, `Check ${obligation} obligation`);
      const projectionDigest = git(checkout, ['rev-parse', 'HEAD^{tree}']);
      const environment = proofReuseEnvironment(path.join(worktree, task.projectRelative), env);
      const environmentDigest = environment.digest;
      const prior = previous?.[obligation];
      const provenance = prior && checkedProjections.get(prior);
      const sameInput = !!provenance && prior?.obligation === obligation && prior.planDigest === planDigest &&
        provenance?.environmentDigest === environmentDigest && provenance.projectionDigest === projectionDigest &&
        provenance.receiptDigest === mathDigest(canonicalMathJson(prior));
      if (sameInput && environment.reusable && provenance.reusable &&
          (prior.passed || hasDeterministicLeanFailure(prior.verification))) {
        const receipt = { ...prior, sourceCommit: source.commit, sourceDigest: source.sourceDigest, reused: true,
          unchangedFailures: prior.passed ? 0 : prior.unchangedFailures + 1 };
        checkedProjections.set(receipt, { ...provenance, receiptDigest: mathDigest(canonicalMathJson(receipt)) });
        return receipt;
      }
      const name = obligation === 'lemma' ? plan.lemma : plan.target;
      const { passed, verification } = await checkProjectedDeclaration(task, checkout, worktree, commit,
        { proofPath: plan.proofPath, theoremName: name, digest: planDigest, missingError: 'math_lemma_projection_missing_declaration' },
      { env: environment.env, signal, timeoutMs: 180_000,
        ...(obligation === 'lemma' ? { expectedDeclarationType: plan.type } : {}) });
      const unchangedFailures = !passed && verification.status === 'failed'
        ? sameInput && !prior.passed ? prior.unchangedFailures + 1 : 1 : 0;
      const receipt = { obligation, sourceCommit: source.commit, sourceDigest: source.sourceDigest, planDigest,
        projectionDigest, unchangedFailures, reused: false, commit, passed, verification };
      const reusable = environment.reusable &&
        proofReuseEnvironment(path.join(worktree, task.projectRelative), environment.env).digest === environmentDigest;
      checkedProjections.set(receipt, { environmentDigest, projectionDigest, reusable,
        receiptDigest: mathDigest(canonicalMathJson(receipt)) });
      return receipt;
    });
  };
  const bridge = await check('bridge');
  // Spend the shared budget on the lemma only after its intended use checks.
  const lemma = bridge.passed ? await check('lemma') : undefined;
  return { plan, bridge, lemma };
}
