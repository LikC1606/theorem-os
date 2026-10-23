import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import { assertSolverSources, commitSolverSources, committedSource, git, withSolverWorktree,
  SolverSourceError, type SolverProblem } from '../src/solver/problem';
import { isSolverSourceOwnershipFeedback, solverSourceFeedback } from '../src/solver/feedback';
import { localExample } from './helpers/solver';

describe('advisory scratch source ownership', () => {
  let directory: string, workspace: string, project: string, problem: SolverProblem;
  const root = (scope: 'repository' | 'project') => scope === 'repository' ? workspace : project;
  const write = (relative: string, content: string) => {
    const file = path.join(workspace, relative);
    fs.mkdirSync(path.dirname(file), { recursive: true }); fs.writeFileSync(file, content);
    return file;
  };
  const scoped = (scope: 'repository' | 'project', relative: string) =>
    scope === 'repository' ? relative : path.join(problem.projectRelative, relative);
  const tracked = (file: string) => git(workspace, ['ls-files', '-z', '--', file]).split('\0').filter(Boolean);
  const tree = (commit: string) => git(workspace, ['ls-tree', '-r', '--name-only', '-z', commit]).split('\0').filter(Boolean);
  const commitFixture = () => {
    git(workspace, ['-c', 'user.name=Scratch Fixture', '-c', 'user.email=scratch@localhost', 'commit',
      '--no-gpg-sign', '--quiet', '-m', 'Prepare disposable tracked scratch']);
    return git(workspace, ['rev-parse', 'HEAD']);
  };
  const unchangedFailure = (reason = 'math_source_outside_ownership') => {
    const before = git(workspace, ['rev-parse', 'HEAD']), index = git(workspace, ['diff', '--cached', '--name-only', '-z']);
    expect(() => assertSolverSources(problem, workspace)).toThrow(reason);
    expect(() => commitSolverSources(problem, workspace)).toThrow(reason);
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(before);
    expect(git(workspace, ['diff', '--cached', '--name-only', '-z'])).toBe(index);
  };

  beforeEach(() => {
    ({ directory, workspace, problem } = localExample('solver-scratch-ownership-'));
    project = path.join(workspace, problem.projectRelative);
  });
  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

  it('reports a doubled project prefix exactly and preserves every byte until its author corrects the path', () => {
    const relative = path.join(problem.projectRelative, problem.projectRelative, '.scratch/tmp/Bridge.lean');
    const content = 'lemma advisory_bridge : True := by trivial\n';
    const file = write(relative, content);
    fs.writeFileSync(path.join(project, 'Submission.lean'), LOCAL_EXAMPLE_PROOF);
    let failure: unknown;
    try { assertSolverSources(problem, workspace); } catch (error) { failure = error; }
    expect(failure).toBeInstanceOf(SolverSourceError);
    expect(failure).toMatchObject({ message: 'math_source_outside_ownership', proofPath: relative });
    const feedback = solverSourceFeedback(problem, workspace)!;
    expect(isSolverSourceOwnershipFeedback(feedback)).toBe(true);
    expect(feedback).toContain(`File: ${relative}\nError: math_source_outside_ownership\n`);
    expect(feedback).toContain(`Project directory: ${project}`);
    expect(feedback).toContain('Check pwd');
    expect(feedback).toContain('moving a file alone does not remove an index or history entry');
    unchangedFailure();
    expect(fs.readFileSync(file, 'utf8')).toBe(content);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toBe(LOCAL_EXAMPLE_PROOF);
    const corrected = path.join(project, '.scratch/tmp/Bridge.lean');
    fs.mkdirSync(path.dirname(corrected), { recursive: true }); fs.renameSync(file, corrected);
    expect(solverSourceFeedback(problem, workspace)).toBeUndefined();
    const commit = commitSolverSources(problem, workspace);
    expect(tree(commit)).not.toContain(path.join(problem.projectRelative, '.scratch/tmp/Bridge.lean'));
    expect(fs.readFileSync(corrected, 'utf8')).toBe(content);
    expect(committedSource(workspace, commit, path.join(problem.projectRelative, 'Submission.lean'))).toBe(LOCAL_EXAMPLE_PROOF);
  });

  it.each(['repository', 'project'] as const)('retains ordinary untracked advisory files at every reserved %s scratch root', scope => {
    const files = ['.scratch/search.py', 'scratch/experiment.c', '.probe/Claim.lean', 'scratch_trial/nested/findings.md', 'scratch_summary'];
    for (const [index, relative] of files.entries()) write(scoped(scope, relative), `advisory experiment ${index}\n`);
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    const commit = commitSolverSources(problem, workspace);
    expect(commit).toBe(problem.baseCommit);
    for (const [index, relative] of files.entries()) {
      expect(fs.readFileSync(path.join(root(scope), relative), 'utf8')).toBe(`advisory experiment ${index}\n`);
      expect(tracked(scoped(scope, relative))).toEqual([]);
      expect(tree(commit)).not.toContain(scoped(scope, relative));
    }
  });

  it.each(['repository', 'project'] as const)('preserves scratch filenames containing spaces, tabs and newlines at the %s root', scope => {
    const files = ['.scratch/two words.txt', 'scratch/tab\tname.py', '.probe/line\nbreak.lean', 'scratch_笔记/含空格 file.txt'];
    for (const relative of files) write(scoped(scope, relative), 'retained exact bytes\n');
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    expect(commitSolverSources(problem, workspace)).toBe(problem.baseCommit);
    for (const relative of files) {
      expect(fs.readFileSync(path.join(root(scope), relative), 'utf8')).toBe('retained exact bytes\n');
      expect(tracked(scoped(scope, relative))).toEqual([]);
    }
  });

  it.each(['repository', 'project'] as const)('retains the existing untracked Probe*.lean convention at the %s root', scope => {
    const relative = scoped(scope, 'ProbeIndependent.lean'), content = 'lemma local_probe : True := by trivial\n';
    const file = write(relative, content);
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    expect(commitSolverSources(problem, workspace)).toBe(problem.baseCommit);
    expect(fs.readFileSync(file, 'utf8')).toBe(content);
    expect(tracked(relative)).toEqual([]); expect(tree(problem.baseCommit)).not.toContain(relative);
  });

  it.each(['repository', 'project'] as const)('commits formal proof sources and notes while keeping %s scratch out of a strict checkout', async scope => {
    const files = ['.scratch/estimate.py', 'scratch/coordinates.txt', '.probe/Trial.lean', 'scratch_route/argument.md', 'ProbeCandidate.lean'];
    for (const relative of files) write(scoped(scope, relative), `advisory-only ${relative}\n`);
    fs.writeFileSync(path.join(project, 'Submission.lean'), LOCAL_EXAMPLE_PROOF);
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'The original targets have saved proof bodies.\n');
    const commit = commitSolverSources(problem, workspace);
    expect(commit).not.toBe(problem.baseCommit);
    expect(committedSource(workspace, commit, path.join(problem.projectRelative, 'Submission.lean'))).toBe(LOCAL_EXAMPLE_PROOF);
    expect(committedSource(workspace, commit, 'RESEARCH.md')).toContain('original targets');
    expect(git(workspace, ['diff', '--name-only', '-z', problem.baseCommit, commit]).split('\0').filter(Boolean).sort())
      .toEqual(['RESEARCH.md', path.join(problem.projectRelative, 'Submission.lean')].sort());
    await withSolverWorktree(workspace, commit, async checkout => {
      expect(() => assertSolverSources(problem, checkout)).not.toThrow();
      expect(git(checkout, ['status', '--porcelain'])).toBe('');
      for (const relative of files) expect(fs.existsSync(path.join(checkout, scoped(scope, relative)))).toBe(false);
    });
    for (const relative of files) expect(fs.readFileSync(path.join(root(scope), relative), 'utf8')).toBe(`advisory-only ${relative}\n`);
  });

  it.each(['repository', 'project'] as const)('rejects a staged scratch file at the %s root without committing it', scope => {
    const relative = scoped(scope, 'scratch_staged/experiment.txt'), file = write(relative, 'staged advisory input\n');
    git(workspace, ['add', '--', relative]); unchangedFailure();
    expect(fs.readFileSync(file, 'utf8')).toBe('staged advisory input\n'); expect(tracked(relative)).toEqual([relative]);
  });

  it.each(['repository', 'project'] as const)('rejects a staged %s scratch file even when the worker deletes its disk copy', scope => {
    const relative = scoped(scope, '.scratch/staged-then-deleted.txt'), file = write(relative, 'index-only advisory input\n');
    git(workspace, ['add', '--', relative]); fs.unlinkSync(file);
    unchangedFailure();
    expect(fs.existsSync(file)).toBe(false);
    expect(git(workspace, ['diff', '--cached', '--name-only', '-z']).split('\0').filter(Boolean)).toContain(relative);
  });

  it.each(['repository', 'project'] as const)('rejects a tracked scratch addition after the frozen base at the %s root', scope => {
    const relative = scoped(scope, '.probe/tracked-experiment.py'), file = write(relative, 'tracked experiment\n');
    git(workspace, ['add', '--', relative]); commitFixture(); unchangedFailure();
    expect(fs.readFileSync(file, 'utf8')).toBe('tracked experiment\n');
    expect(tracked(relative)).toEqual([relative]);
  });

  it.each(['repository', 'project'] as const)('rejects modifications to a pre-existing tracked %s scratch path', scope => {
    const relative = scoped(scope, 'scratch_previous/data.txt'), file = write(relative, 'frozen tracked input\n');
    git(workspace, ['add', '--', relative]); problem = { ...problem, baseCommit: commitFixture() };
    fs.writeFileSync(file, 'modified tracked input\n'); unchangedFailure();
    expect(fs.readFileSync(file, 'utf8')).toBe('modified tracked input\n');
  });

  it.each(['repository', 'project'] as const)('rejects an untracked %s scratch symlink without following or removing it', scope => {
    const outside = path.join(directory, 'outside-evidence.txt'); fs.writeFileSync(outside, 'immutable external evidence\n');
    const file = path.join(root(scope), 'scratch_redirect'); fs.symlinkSync(outside, file);
    unchangedFailure();
    expect(fs.lstatSync(file).isSymbolicLink()).toBe(true);
    expect(fs.readFileSync(outside, 'utf8')).toBe('immutable external evidence\n');
  });

  it.each(['repository', 'project'] as const)('rejects a linked %s scratch directory even when its target contains ordinary files', scope => {
    const outside = path.join(directory, 'outside-directory'); fs.mkdirSync(outside);
    fs.writeFileSync(path.join(outside, 'findings.txt'), 'outside directory evidence\n');
    const file = path.join(root(scope), '.scratch'); fs.symlinkSync(outside, file, 'dir'); unchangedFailure();
    expect(fs.lstatSync(file).isSymbolicLink()).toBe(true);
    expect(fs.readFileSync(path.join(outside, 'findings.txt'), 'utf8')).toBe('outside directory evidence\n');
  });

  it('rejects a symlink inside a reserved scratch tree while preserving ordinary sibling findings', () => {
    const sibling = write('.scratch/kept.txt', 'ordinary advisory sibling\n');
    const file = path.join(workspace, '.scratch', 'redirect.txt');
    fs.symlinkSync(path.join(project, 'Challenge.lean'), file); unchangedFailure();
    expect(fs.readFileSync(sibling, 'utf8')).toBe('ordinary advisory sibling\n');
    expect(fs.lstatSync(file).isSymbolicLink()).toBe(true);
    expect(fs.existsSync(path.join(project, 'Challenge.lean'))).toBe(true);
  });

  it.each([
    'notes/.scratch/findings.txt', 'notes/scratch/experiment.py', 'generated/.probe/typecheck.lean',
    'generated/scratch_old/data.txt', 'generated/addition/Nested/.scratch/findings.md',
    'generated/addition/Nested/scratch_branch/experiment.c',
  ])('rejects scratch disguised under an unauthorized parent: %s', relative => {
    const file = write(relative, 'not at an authorized scratch root\n'); unchangedFailure();
    expect(fs.readFileSync(file, 'utf8')).toBe('not at an authorized scratch root\n');
  });

  it.each(['ordinary.lean', 'generated/addition/Unowned.lean', '.scratchy/findings.txt', 'scratchy/data.py', '.probe_extra/Trial.lean'])
  ('rejects ordinary out-of-scope source or an unreserved lookalike: %s', relative => {
    const allowed = write('.scratch/retained.txt', 'keep this independent advisory result\n');
    const file = write(relative, 'out of source ownership\n'); unchangedFailure();
    expect(fs.readFileSync(allowed, 'utf8')).toBe('keep this independent advisory result\n');
    expect(fs.readFileSync(file, 'utf8')).toBe('out of source ownership\n');
  });

  it.each(['scratch_owned.lean', '.scratch/Official.lean', 'ProbeOfficial.lean'])
  ('commits a formally owned source named %s instead of treating it as disposable scratch', async relative => {
    const content = 'lemma official_owned_helper : True := by trivial\n';
    const file = write(path.join(problem.projectRelative, relative), content);
    problem = { ...problem, ownedFiles: [...problem.ownedFiles, relative],
      declarations: { ...problem.declarations, [relative]: [] },
      sourceStructure: { ...problem.sourceStructure, [relative]: mathDigest('') },
      sourceImports: { ...problem.sourceImports, [relative]: [] } };
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    const commit = commitSolverSources(problem, workspace), repositoryPath = path.join(problem.projectRelative, relative);
    expect(commit).not.toBe(problem.baseCommit);
    expect(tracked(repositoryPath)).toEqual([repositoryPath]);
    expect(committedSource(workspace, commit, repositoryPath)).toBe(content); expect(fs.readFileSync(file, 'utf8')).toBe(content);
    await withSolverWorktree(workspace, commit, async checkout => {
      expect(() => assertSolverSources(problem, checkout)).not.toThrow();
      expect(fs.readFileSync(path.join(checkout, repositoryPath), 'utf8')).toBe(content);
    });
  });

  it.each(['scratch_frozen.lean', '.probe/Official.lean', 'ProbeFrozen.lean'])
  ('enforces the frozen declaration contract for an owned source named %s', relative => {
    const source = fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8');
    const file = write(path.join(problem.projectRelative, relative), source);
    problem = { ...problem, ownedFiles: [...problem.ownedFiles, relative],
      declarations: { ...problem.declarations, [relative]: problem.declarations['Submission.lean'] },
      sourceStructure: { ...problem.sourceStructure, [relative]: problem.sourceStructure['Submission.lean'] },
      sourceImports: { ...problem.sourceImports, [relative]: problem.sourceImports!['Submission.lean'] } };
    fs.writeFileSync(file, source.replace('n + 0 = n', 'n + 0 = n + 1'));
    unchangedFailure('math_original_declaration_changed');
    expect(fs.readFileSync(file, 'utf8')).toContain('n + 0 = n + 1');
  });

  it.each(['scratch_trusted.txt', '.scratch/Trusted.txt', 'ProbeTrusted.lean'])
  ('enforces trusted bytes for a reserved-looking protected file named %s', relative => {
    const file = write(path.join(problem.projectRelative, relative), 'frozen protected bytes\n');
    problem = { ...problem, trustedFiles: { ...problem.trustedFiles, [relative]: mathDigest('frozen protected bytes\n') } };
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    expect(fs.readFileSync(file, 'utf8')).toBe('frozen protected bytes\n');
    fs.writeFileSync(file, 'tampered protected bytes\n'); unchangedFailure('math_trusted_source_changed');
    expect(fs.readFileSync(file, 'utf8')).toBe('tampered protected bytes\n');
  });
});
