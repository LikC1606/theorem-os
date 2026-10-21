import { describe, expect, it } from 'vitest';
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
