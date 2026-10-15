import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { bootstrapLocalExample, readLocalExampleReceipt, LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import { readSolverProblem, assertSolverSources } from '../src/solver/problem';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
function fixture() {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-example-'))); roots.push(root);
  const receipt = bootstrapLocalExample(path.join(root, 'workspace'));
  return { root, receipt };
}
describe('local Lean tutorial', () => {
  it('starts with two unfinished targets and no external packages', () => {
    const { receipt } = fixture();
    const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
    expect(problem.kind).toBe('example');
    expect(problem.targets.map(target => target.theoremName)).toEqual(['Tutorial.add_zero', 'Tutorial.zero_add']);
    expect(fs.readFileSync(path.join(receipt.projectRoot, 'Submission.lean'), 'utf8').match(/sorry/g)).toHaveLength(2);
    expect(JSON.parse(fs.readFileSync(path.join(receipt.projectRoot, 'lake-manifest.json'), 'utf8')).packages).toEqual([]);
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).not.toThrow();
    fs.writeFileSync(path.join(receipt.projectRoot, 'Submission.lean'), LOCAL_EXAMPLE_PROOF);
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).not.toThrow();
  });
  it('refuses to overwrite an existing workspace', () => {
    const { receipt } = fixture();
    expect(() => bootstrapLocalExample(receipt.workspaceRoot)).toThrow('already exists');
    expect(readLocalExampleReceipt(receipt.activeProblemPath).contract.problemId).toBe('tutorial-addition');
  });
  it.each(['contract', 'publicObligations', 'projectRoot'])('rejects a redefined %s in the tutorial receipt', key => {
    const { receipt } = fixture();
    fs.writeFileSync(receipt.activeProblemPath, JSON.stringify({ ...receipt,
      [key]: key === 'contract' ? { ...receipt.contract, formalStatement: 'True' } : key === 'publicObligations' ? [] : receipt.workspaceRoot }));
    expect(() => readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath)).toThrow('identity changed');
  });
  it('rejects changes to protected project inputs and target declarations', () => {
    const { receipt } = fixture();
    const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
    fs.writeFileSync(path.join(receipt.projectRoot, 'Submission.lean'), LOCAL_EXAMPLE_PROOF.replace('n + 0 = n', 'True'));
    expect(() => assertSolverSources(problem, receipt.workspaceRoot)).toThrow('math_original_declaration_changed');
    fs.appendFileSync(path.join(receipt.projectRoot, 'lean-toolchain'), '\n');
    expect(() => readLocalExampleReceipt(receipt.activeProblemPath)).toThrow('protected file changed');
  });
});
