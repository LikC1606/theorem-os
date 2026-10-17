import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { readLemmaPlan } from '../src/solver/lemma';
import type { SolverProblem } from '../src/solver/problem';
import { parseCooperationPlan } from '../src/solver/tasks';

const theoremName = 'Submission.ErdosSupersingularPrimes.k₀';
const problem = {
  ownedFiles: ['Submission.lean'],
  targets: [{ proofPath: 'Submission.lean', theoremName }],
  declarations: { 'Submission.lean': [{ name: 'k₀', header: 'k₀ : True' }] },
} as unknown as SolverProblem;
const helper = { id: 'bridge', kind: 'lemma', objective: 'Prove the bridge',
  theoremName: 'Submission.桥梁₂', type: 'True', dependsOn: [] };
const goal = { id: 'goal', kind: 'goal', objective: 'Prove the frozen original target',
  theoremName, dependsOn: ['bridge'] };
const lemmaPlan = { proofPath: 'Submission.lean', target: theoremName,
  lemma: 'Submission.桥梁₂', type: 'True' };
const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

function researchWorkspace(plan: object): string {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-lean-plan-names-')));
  roots.push(root);
  fs.writeFileSync(path.join(root, 'RESEARCH.md'), JSON.stringify(plan));
  return root;
}

describe('Unicode proof targets in cooperative plans', () => {
  it('preserves the frozen subscript target and accepts a Unicode helper', () => {
    const plan = parseCooperationPlan(problem, { tasks: [helper, goal] });
    expect(plan.tasks).toEqual([
      { ...helper, proofPath: 'Submission.lean', revision: 0 },
      { ...goal, proofPath: 'Submission.lean', revision: 0 },
    ]);
  });

  it.each(['Submission.ErdosSupersingularPrimes.k₁', 'Submission.ErdosSupersingularPrimes.k0',
    'Other.ErdosSupersingularPrimes.k₀'])(
    'rejects a changed original target even when it is a valid Lean name: %s', changedName => {
      expect(() => parseCooperationPlan(problem, { tasks: [helper,
        { ...goal, proofPath: 'Submission.lean', theoremName: changedName }] }))
        .toThrow('math_plan_changed_original_target');
    }
  );

  it.each(['', 'Submission..桥梁₂', 'Submission.桥梁₂ ', 'Submission.1桥梁₂',
    'Submission.桥梁₂\n#eval 0', 'Submission.桥梁₂; theorem injected'])(
    'rejects malformed helper targets: %j', invalidName => {
      expect(() => parseCooperationPlan(problem, { tasks: [{ ...helper, theoremName: invalidName }, goal] }))
        .toThrow('math_plan_invalid_proof_target');
    }
  );

  it.each(['../Outside.lean', '/tmp/Outside.lean'])(
    'rejects a proof path outside the owned files: %s', proofPath => {
      expect(() => parseCooperationPlan(problem, { tasks: [{ ...helper, proofPath }, goal] }))
        .toThrow('math_plan_invalid_proof_target');
    }
  );

  it('does not let a Unicode helper reuse an original declaration basename', () => {
    expect(() => parseCooperationPlan(problem, { tasks: [{ ...helper, theoremName: 'Submission.k₀' }, goal] }))
      .toThrow('math_plan_invalid_helper_type');
  });
});

describe('Unicode helper names in lemma plans', () => {
  it('preserves a Unicode helper and exact frozen target in a research proposal', () => {
    expect(readLemmaPlan(problem, researchWorkspace(lemmaPlan))).toEqual(lemmaPlan);
  });

  it.each([
    { lemma: 'Submission..桥梁₂' },
    { lemma: 'Submission.桥梁₂\n#eval 0' },
    { target: 'Submission.ErdosSupersingularPrimes.k0' },
    { proofPath: '../Outside.lean' },
    { proofPath: '/tmp/Outside.lean' },
  ])('rejects malformed names or proposals outside the frozen target: %j', changes => {
    expect(() => readLemmaPlan(problem, researchWorkspace({ ...lemmaPlan, ...changes })))
      .toThrow('math_lemma_plan_invalid');
  });
});
