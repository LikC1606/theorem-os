import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { bootstrapLeanTask } from '../src/math/leanTask';
import { inspectLeanDeclarationRegions } from '../src/math/leanSource';
import { applyTaskChanges, createTaskSourceProjector, taskChanges } from '../src/solver/cooperativeProof';
import { commitSolverSources, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { captureProofReferences, proofReferencesUnchanged } from '../src/solver/proofReferences';
import type { CooperativeTask } from '../src/solver/tasks';
import { temporaryDirectory } from './helpers/files';

describe('punctuation in cooperative declaration identities', () => {
  let directory: string, workspace: string, file: string, problem: SolverProblem;
  const original = 'namespace Submission\ntheorem goal : True := by sorry\nend Submission\n';
  const helper = (name: string): CooperativeTask => ({ id: 'helper', kind: 'lemma', revision: 0,
    objective: 'Prove the helper', proofPath: 'Submission.lean', theoremName: `Submission.${name}`,
    type: 'True', dependsOn: [] });
  const save = (declarations: string) => {
    const source = original.replace('theorem goal', declarations + 'theorem goal');
    fs.writeFileSync(file, source);
    return { source, commit: commitSolverSources(problem, workspace) };
  };

  beforeEach(() => {
    directory = temporaryDirectory('lean-declaration-identity-');
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLeanTask(workspace, { source: original, task: 'Prove the goal.' });
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    file = path.join(receipt.projectRoot, 'Submission.lean');
  });
  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

  it('projects each distinct helper and replays the changes without name collisions', () => {
    const names = ['probe?', 'probe', 'probe!'];
    const { source, commit } = save(names.map(name => `lemma ${name} : True := by trivial\n`).join(''));
    const changes = taskChanges(problem, workspace, commit, helper('probe?'), { seedCommit: problem.baseCommit });
    expect(changes.map(change => change.name)).toEqual(names);
    const project = createTaskSourceProjector(problem, workspace, commit);
    for (const name of names) {
      const projected = project(helper(name), []).get('Submission.lean')!;
      expect(inspectLeanDeclarationRegions(projected).map(item => item.name)).toEqual(names);
    }
    fs.writeFileSync(file, original);
    applyTaskChanges(problem, workspace, changes);
    expect(fs.readFileSync(file, 'utf8')).toBe(source);
  });

  it('still rejects genuine duplicate names when collecting changes or projecting a target', () => {
    const { commit } = save('lemma probe? : True := by trivial\nlemma probe? : True := by trivial\n');
    expect(() => taskChanges(problem, workspace, commit, helper('probe?'), { seedCommit: problem.baseCommit }))
      .toThrow('math_task_ambiguous_declaration');
    expect(() => createTaskSourceProjector(problem, workspace, commit)(helper('probe?'), []))
      .toThrow('math_task_ambiguous_declaration');
  });

  it.each(['?', '!'])('abstracts %s inputs and removes their wrapper chains without touching the plain name', suffix => {
    const input = `premise${suffix}`;
    const { source, commit } = save(`lemma ${input} : True := by trivial\n` +
      `lemma wrapper : True := ${input}\nlemma wrapper_chain : True := wrapper\n` +
      'lemma premise : True := by trivial\nlemma independent : True := premise\n' +
      `lemma consumer : True := Submission.${input}\n`);
    const projected = createTaskSourceProjector(problem, workspace, commit)(
      { ...helper('consumer'), dependsOn: ['input'], conditional: true }, [], [{ ...helper(input), id: 'input' }])
      .get('Submission.lean')!;
    expect(projected).toContain(`lemma consumer (${input} : True) : True := ${input}`);
    expect(projected).not.toContain(`Submission.${input}`);
    expect(inspectLeanDeclarationRegions(projected).map(item => item.name)).toEqual(['premise', 'independent', 'consumer']);
    expect(fs.readFileSync(file, 'utf8')).toBe(source);
  });

  it.each(['?', '!'])('retains a %s helper wrapper when only the plain-name peer is unfinished', suffix => {
    const { commit } = save('lemma premise : True := by sorry\n' +
      `lemma premise${suffix} : True := by trivial\nlemma wrapper : True := premise${suffix}\n` +
      'lemma consumer : True := wrapper\n');
    const projected = createTaskSourceProjector(problem, workspace, commit)(helper('consumer'), []).get('Submission.lean')!;
    expect(inspectLeanDeclarationRegions(projected).map(item => item.name)).toEqual([`premise${suffix}`, 'wrapper', 'consumer']);
  });

  it.each(['?', '!'])('orders a conditional consumer after its exact %s input during integration', suffix => {
    const input = `premise${suffix}`;
    const before = 'theorem goal : True := by sorry\n', after = `theorem goal : True := ${input}\n`;
    fs.writeFileSync(file, original.replace('end Submission', `lemma ${input} : True := by trivial\nend Submission`));
    applyTaskChanges(problem, workspace, [{ file: 'Submission.lean', name: 'goal', before, after }], [], [helper(input)]);
    const integrated = fs.readFileSync(file, 'utf8');
    expect(inspectLeanDeclarationRegions(integrated).map(item => item.name)).toEqual([input, 'goal']);
    expect(integrated).toContain(after);
  });

  it.each(['?', '!'])('fingerprints the exact %s dependency when deciding whether evidence is reusable', suffix => {
    const input = `premise${suffix}`;
    const { source, commit } = save('lemma premise : True := by trivial\n' +
      `lemma ${input} : True := by trivial\nlemma consumer : True := ${input}\n`);
    // These references stand in for Lean-selected evidence; source text only fingerprints their declarations.
    const references = captureProofReferences(problem, workspace, commit, { file: 'Submission.lean', name: 'Submission.consumer' },
      { statement: [], proof: [{ file: 'Submission.lean', name: `Submission.${input}` }] }, 'environment')!;
    expect(references.inputs.map(item => item.name).sort()).toEqual(['consumer', input].sort());
    fs.writeFileSync(file, source.replace('lemma premise : True := by trivial', 'lemma premise : True := by exact True.intro'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), references, 'environment')).toBe(true);
    fs.writeFileSync(file, source.replace(`lemma ${input} : True := by trivial`, `lemma ${input} : True := by exact True.intro`));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), references, 'environment')).toBe(false);
  });
});
