import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import type { RuntimeMathAssignment } from '../src/common/types/team/mathRuntimeContracts';
import type { ProjectGitResearchTeamAssignmentReceipt } from '../src/project-git';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { MathematicsVerifierBatchResult } from '../src/math/verifier';
import {
  commitMathV2PromotionWorktree,
  isHostRuntimeRecord,
  parseMathPorcelainV1Z,
  prepareMathV2Promotion,
  promoteMathV2DraftToWorktree,
  verifyMathV2SourceCommit,
} from '../src/math/mathIntegrationPromotion';

describe('v2 Git promotion preflight', () => {
  const roots: string[] = [];
  afterEach(() => roots.splice(0).forEach((root) => fs.rmSync(root, { recursive: true, force: true })));
  const fixture = () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-promotion-')));
    roots.push(root);
    const project = path.join(root, 'project');
    const worktree = path.join(root, 'worktree');
    const draft = path.join(root, 'draft');
    fs.mkdirSync(project);
    fs.mkdirSync(worktree);
    fs.mkdirSync(draft);
    fs.writeFileSync(path.join(draft, 'Main.lean'), 'def x := 1\n');
    const assignment = {
      assignmentId: 'assignment',
      baseCommit: 'a'.repeat(40),
      sourceRootRelative: 'Generated/A',
      draftRoot: draft,
    } as unknown as RuntimeMathAssignment;
    const receipt = {
      schema: 'deepscientist.research_team_assignment.v2',
      state: 'accepted',
      assignmentId: 'assignment',
      preparedGit: { branch: 'worker/assignment', worktreePath: worktree, baseCommit: 'a'.repeat(40) },
    } as unknown as ProjectGitResearchTeamAssignmentReceipt;
    return { project, worktree, draft, assignment, receipt };
  };
  it('requires durable branch/worktree evidence', () => {
    const f = fixture();
    expect(() => prepareMathV2Promotion({ ...f.receipt, preparedGit: undefined }, f.assignment, f.project)).toThrow(
      'pending_worktree'
    );
  });
  it('promotes verified draft files and rejects hash drift before writing', () => {
    const f = fixture();
    const plan = prepareMathV2Promotion(f.receipt, f.assignment, f.project);
    const content = fs.readFileSync(path.join(f.draft, 'Main.lean'));
    expect(
      promoteMathV2DraftToWorktree(
        plan,
        f.assignment,
        [{ pathRelative: 'Main.lean', contentSha256: mathDigest(content) }],
        f.project
      )
    ).toEqual(['Generated/A/Main.lean']);
    expect(fs.readFileSync(path.join(f.worktree, 'Generated/A/Main.lean'))).toEqual(content);
    fs.rmSync(path.join(f.worktree, 'Generated/A'), { recursive: true, force: true });
    expect(() =>
      promoteMathV2DraftToWorktree(
        plan,
        f.assignment,
        [{ pathRelative: 'Main.lean', contentSha256: '0'.repeat(64) }],
        f.project
      )
    ).toThrow('hash');
    expect(fs.existsSync(path.join(f.worktree, 'Generated/A/Main.lean'))).toBe(false);
  });
  it('reuses an exact clean private commit after a crash', () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-promotion-git-')));
    roots.push(root);
    execFileSync('git', ['-C', root, 'init', '--quiet']);
    const branch = 'deepscientist/math/assignment';
    execFileSync('git', ['-C', root, 'checkout', '-b', branch]);
    fs.writeFileSync(path.join(root, 'base.txt'), 'base\n');
    execFileSync('git', ['-C', root, 'add', '--all']);
    execFileSync('git', [
      '-C',
      root,
      '-c',
      'user.name=Test',
      '-c',
      'user.email=test@invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      'base',
    ]);
    const baseCommit = execFileSync('git', ['-C', root, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
    const sourcePath = 'Generated/A/Main.lean';
    const source = 'theorem target : True := by trivial\n';
    fs.mkdirSync(path.join(root, 'Generated/A'), { recursive: true });
    fs.writeFileSync(path.join(root, sourcePath), source);
    const request = {
      worktreePath: root,
      includePaths: [sourcePath],
      expectedFiles: [{ pathRelative: sourcePath, contentSha256: mathDigest(source) }],
      assignmentId: 'assignment',
      branch,
      baseCommit,
    };

    const first = commitMathV2PromotionWorktree(request);
    const notes = path.join(root, 'Generated/A/RESEARCH.md');
    fs.writeFileSync(notes, 'Retained mathematical progress\n');
    const replay = commitMathV2PromotionWorktree(request);
    expect(replay).toEqual({ commit: first.commit, replayed: true });
    expect(fs.readFileSync(notes, 'utf8')).toBe('Retained mathematical progress\n');

    // Run 23: host-owned proof-session records beside an already committed
    // proof made every integrate fail. They are tolerated; other paths are not.
    const records = path.join(root, '.deepscientist/math/worker-proof');
    fs.mkdirSync(records, { recursive: true });
    fs.writeFileSync(path.join(records, 'session.attempts.jsonl'), '{}\n');
    fs.writeFileSync(path.join(records, 'session.identity.json'), '{}\n');
    expect(commitMathV2PromotionWorktree(request)).toEqual({ commit: first.commit, replayed: true });
    // The science runtime manifest lean_workspace writes in the root is host state too.
    fs.writeFileSync(path.join(root, '.deepscientist/project.json'), '{}\n');
    fs.writeFileSync(path.join(root, '.deepscientist/.gitignore'), '/artifact-repo/\n');
    expect(commitMathV2PromotionWorktree(request)).toEqual({ commit: first.commit, replayed: true });
    fs.mkdirSync(path.join(root, '.deepscientist/math/other'), { recursive: true });
    fs.writeFileSync(path.join(root, '.deepscientist/math/other/Main.lean'), 'axiom unsafe : False\n');
    expect(() => commitMathV2PromotionWorktree(request)).toThrow();
    fs.rmSync(path.join(root, '.deepscientist/math/other'), { recursive: true });

    fs.writeFileSync(path.join(root, 'unexpected.lean'), 'axiom unsafe : False\n');
    expect(() => commitMathV2PromotionWorktree(request)).toThrow();
    fs.unlinkSync(path.join(root, 'unexpected.lean'));

    fs.writeFileSync(path.join(root, sourcePath), `${source}-- drift\n`);
    expect(() => commitMathV2PromotionWorktree(request)).toThrow();
  });

  it('verifies a historical canonical commit in a detached checkout', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-verification-git-')));
    roots.push(root);
    execFileSync('git', ['-C', root, 'init', '--quiet']);
    execFileSync('git', ['-C', root, 'checkout', '-b', 'main']);
    const sourcePath = 'Generated/A/Main.lean';
    const source = 'theorem target : True := by trivial\n';
    fs.mkdirSync(path.join(root, 'Generated/A'), { recursive: true });
    fs.writeFileSync(path.join(root, sourcePath), source);
    execFileSync('git', ['-C', root, 'add', '--all']);
    execFileSync('git', [
      '-C',
      root,
      '-c',
      'user.name=Test',
      '-c',
      'user.email=test@invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      'proof',
    ]);
    const targetCommit = execFileSync('git', ['-C', root, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
    fs.writeFileSync(path.join(root, 'later.txt'), 'later\n');
    execFileSync('git', ['-C', root, 'add', '--all']);
    execFileSync('git', [
      '-C',
      root,
      '-c',
      'user.name=Test',
      '-c',
      'user.email=test@invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      'later',
    ]);
    const packagesRoot = path.join(root, '.lake', 'packages');
    fs.mkdirSync(packagesRoot, { recursive: true });
    const statementHash = '1'.repeat(64);
    const declarationHash = '2'.repeat(64);
    const contentSha256 = mathDigest(source);
    const result = await verifyMathV2SourceCommit(
      {
        worktreePath: root,
        targetCommit,
        items: [
          {
            id: 'assignment:target',
            proofPath: sourcePath,
            contentSha256,
            theoremName: 'target',
            statementHash,
            expectedSourceDeclarationHash: declarationHash,
          },
        ],
      },
      async (request, options) => {
        expect(options?.trustedLakePackagesRoots).toEqual([packagesRoot]);
        expect(request.projectRoot).not.toBe(root);
        expect(execFileSync('git', ['-C', request.projectRoot, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim()).toBe(
          targetCommit
        );
        return {
          schema: 'deepscientist.mathematics.verification-batch/v1',
          sessionId: 'session',
          status: 'kernel_verified',
          targetCommit,
          startedAt: 1,
          checkedAt: 2,
          durationMs: 1,
          events: [],
          results: [
            {
              status: 'kernel_verified',
              targetCommit,
              statementHash,
              claim: 'statement',
              proofHash: contentSha256,
              proofPath: sourcePath,
              theoremName: 'target',
              sourceDeclarationHash: declarationHash,
              statementBinding: 'caller-bound-to-committed-declaration',
              toolchain: { lean: 'test' },
              verifier: 'lean-kernel',
              goalsRemaining: 0,
              sorryCount: 0,
              admitCount: 0,
              axioms: [],
              checkedAt: 2,
              checkId: 'assignment:target',
              receiptId: 'receipt',
              sessionId: 'session',
            },
          ],
        };
      }
    );
    expect(result).toMatchObject({ verified: true, disposition: 'verified', receipts: [{ targetCommit, sourcePath }] });
    expect(
      execFileSync('git', ['-C', root, 'worktree', 'list', '--porcelain'], { encoding: 'utf8' }).match(/^worktree /gmu)
    ).toHaveLength(1);
  });

  it('classifies a complete Lean rejection separately from an incomplete check', async () => {
    const f = fixture();
    execFileSync('git', ['-C', f.project, 'init', '--quiet']);
    fs.mkdirSync(path.join(f.project, 'Generated', 'A'), { recursive: true });
    fs.writeFileSync(path.join(f.project, 'Generated', 'A', 'Main.lean'), 'theorem target : True := by sorry\n');
    execFileSync('git', ['-C', f.project, 'add', '--all']);
    execFileSync('git', [
      '-C',
      f.project,
      '-c',
      'user.name=Test',
      '-c',
      'user.email=test@invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      'candidate',
    ]);
    const targetCommit = execFileSync('git', ['-C', f.project, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
    const content = fs.readFileSync(path.join(f.project, 'Generated', 'A', 'Main.lean'));
    const base = {
      targetCommit,
      statementHash: '1'.repeat(64),
      claim: 'statement' as const,
      proofHash: mathDigest(content),
      proofPath: 'Generated/A/Main.lean',
      theoremName: 'target',
      sourceDeclarationHash: '2'.repeat(64),
      statementBinding: 'caller-bound-to-committed-declaration' as const,
      toolchain: { lean: 'test' },
      verifier: 'lean-kernel' as const,
      goalsRemaining: 1,
      sorryCount: 1,
      admitCount: 0,
      axioms: [],
      checkedAt: 2,
      checkId: 'assignment:target',
      receiptId: 'receipt',
      sessionId: 'session',
    };
    const rejected = await verifyMathV2SourceCommit(
      {
        worktreePath: f.project,
        targetCommit,
        items: [
          {
            id: 'assignment:target',
            proofPath: base.proofPath,
            contentSha256: base.proofHash,
            theoremName: 'target',
            statementHash: base.statementHash,
            expectedSourceDeclarationHash: base.sourceDeclarationHash,
          },
        ],
      },
      async () => ({
        schema: 'deepscientist.mathematics.verification-batch/v1',
        sessionId: 'session',
        status: 'failed',
        targetCommit,
        startedAt: 1,
        checkedAt: 2,
        durationMs: 1,
        events: [],
        results: [{ status: 'failed', error: 'sorry remains', ...base }],
      })
    );
    expect(rejected).toMatchObject({
      verified: false,
      disposition: 'candidate_rejected',
      evidence: { disposition: 'candidate_rejected' },
    });
    const pending = await verifyMathV2SourceCommit(
      {
        worktreePath: f.project,
        targetCommit,
        items: [
          {
            id: 'assignment:target',
            proofPath: base.proofPath,
            contentSha256: base.proofHash,
            theoremName: 'target',
            statementHash: base.statementHash,
            expectedSourceDeclarationHash: base.sourceDeclarationHash,
          },
        ],
      },
      async () => ({
        schema: 'deepscientist.mathematics.verification-batch/v1',
        sessionId: 'session',
        status: 'unavailable',
        targetCommit,
        startedAt: 1,
        checkedAt: 2,
        durationMs: 1,
        events: [],
        results: [],
      })
    );
    expect(pending).toMatchObject({ verified: false, disposition: 'pending', evidence: { disposition: 'pending' } });
    for (const [batchStatus, status] of [
      ['blocked', 'blocked'],
      ['unavailable', 'unavailable'],
      ['failed', 'failed'],
      ['kernel_verified', 'blocked'],
      ['kernel_verified', 'unavailable'],
    ] as const) {
      // Each invocation inspects the same Git checkout; keep the fixture operations sequential.
      // eslint-disable-next-line no-await-in-loop
      const diagnosticResult = await verifyMathV2SourceCommit(
        {
          worktreePath: f.project,
          targetCommit,
          items: [
            {
              id: base.checkId,
              proofPath: base.proofPath,
              contentSha256: base.proofHash,
              theoremName: 'target',
              statementHash: base.statementHash,
              expectedSourceDeclarationHash: base.sourceDeclarationHash,
            },
          ],
        },
        async () => ({
          schema: 'deepscientist.mathematics.verification-batch/v1',
          sessionId: 'session',
          status: batchStatus,
          targetCommit,
          startedAt: 1,
          checkedAt: 2,
          durationMs: 1,
          events: [],
          results: [
            {
              ...base,
              status,
              error: 'Lean exited with status 1.',
              stderrPreview: "git: 'remote-https' is not a git command.",
              stdoutPreview: 'mathlib: cloning dependency',
            },
          ],
        })
      );
      expect(diagnosticResult.disposition).toBe(status === 'failed' ? 'candidate_rejected' : 'pending');
      expect(diagnosticResult.diagnostics).toContain("git: 'remote-https' is not a git command.");
      expect(diagnosticResult.diagnostics).toContain('mathlib: cloning dependency');
      expect(diagnosticResult.evidence?.diagnostics).toBe(diagnosticResult.diagnostics);
    }
    const longDiagnostic = await verifyMathV2SourceCommit(
      {
        worktreePath: f.project,
        targetCommit,
        items: [
          {
            id: base.checkId,
            proofPath: base.proofPath,
            contentSha256: base.proofHash,
            theoremName: 'target',
            statementHash: base.statementHash,
            expectedSourceDeclarationHash: base.sourceDeclarationHash,
          },
        ],
      },
      async () => ({
        schema: 'deepscientist.mathematics.verification-batch/v1',
        sessionId: 'session',
        status: 'blocked',
        targetCommit,
        startedAt: 1,
        checkedAt: 2,
        durationMs: 1,
        events: [],
        results: [
          {
            ...base,
            status: 'blocked',
            error: 'dependency unavailable',
            stderrPreview: 'x'.repeat(20000) + ' meaningful tail',
            stdoutPreview: 'separate stdout diagnostic',
          },
        ],
      })
    );
    expect(longDiagnostic.diagnostics!.length).toBeLessThanOrEqual(8192);
    expect(longDiagnostic.diagnostics).toContain('meaningful tail');
    expect(longDiagnostic.diagnostics).toContain('separate stdout diagnostic');
  });

  it('preserves porcelain status spaces and rename paths', () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-porcelain-')));
    roots.push(root);
    execFileSync('git', ['-C', root, 'init', '--quiet']);
    fs.writeFileSync(path.join(root, 'a file.txt'), 'x\n');
    execFileSync('git', ['-C', root, 'add', '--all']);
    execFileSync('git', [
      '-C',
      root,
      '-c',
      'user.name=Test',
      '-c',
      'user.email=test@invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      'base',
    ]);
    execFileSync('git', ['-C', root, 'mv', 'a file.txt', 'RESEARCH.md']);
    fs.appendFileSync(path.join(root, 'RESEARCH.md'), 'changed\n');
    fs.writeFileSync(path.join(root, '中文\n.txt'), 'new\n');
    const encoded = execFileSync('git', ['-C', root, 'status', '--porcelain=v1', '-z', '--untracked-files=all'], {
      encoding: 'buffer',
    });
    expect(parseMathPorcelainV1Z(encoded)).toEqual([
      { indexStatus: 'R', worktreeStatus: 'M', pathRelative: 'RESEARCH.md', originalPathRelative: 'a file.txt' },
      { indexStatus: '?', worktreeStatus: '?', pathRelative: '中文\n.txt' },
    ]);
  });

  it('treats only untracked Lean trace projections as host runtime records', () => {
    // Run 23 attempt 15: certification left these in the Team root.
    const untracked = (pathRelative: string) => ({ indexStatus: '?', worktreeStatus: '?', pathRelative });
    expect(isHostRuntimeRecord(untracked('mathematics/verification-trace.json'))).toBe(true);
    expect(isHostRuntimeRecord(untracked('mathematics/report-traces/verification-0123456789abcdef0123.json'))).toBe(
      true
    );
    expect(isHostRuntimeRecord(untracked('mathematics/report-traces/other.json'))).toBe(false);
    expect(isHostRuntimeRecord(untracked('mathematics/Proof.lean'))).toBe(false);
    // A tracked trace that was modified is proof-branch content, not host state.
    expect(
      isHostRuntimeRecord({
        indexStatus: ' ',
        worktreeStatus: 'M',
        pathRelative: 'mathematics/verification-trace.json',
      })
    ).toBe(false);
  });

  it.each([
    ['empty source', '', { status: 'failed', error: 'missing theorem' }],
    ['comment-only source', '-- no declaration\n', { status: 'failed', error: 'missing theorem' }],
    ['unfinished proof', 'theorem target : True := by sorry\n', { sorryCount: 1 }],
    ['explicit axiom', 'axiom unsafeAx : True\ntheorem target : True := unsafeAx\n', { axioms: ['unsafeAx'] }],
    ['wrong theorem', 'theorem target : True := by trivial\n', { theoremName: 'other' }],
    ['wrong statement', 'theorem target : True := by trivial\n', { statementHash: '8'.repeat(64) }],
    ['wrong declaration', 'theorem target : True := by trivial\n', { sourceDeclarationHash: '7'.repeat(64) }],
  ] as const)('rejects %s even when a certifier returns a receipt-shaped result', async (_label, source, overrides) => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-verification-reject-')));
    roots.push(root);
    execFileSync('git', ['-C', root, 'init', '--quiet']);
    execFileSync('git', ['-C', root, 'checkout', '-b', 'main']);
    const sourcePath = 'Generated/A/Main.lean';
    fs.mkdirSync(path.dirname(path.join(root, sourcePath)), { recursive: true });
    fs.writeFileSync(path.join(root, sourcePath), source);
    execFileSync('git', ['-C', root, 'add', '--all']);
    execFileSync('git', [
      '-C',
      root,
      '-c',
      'user.name=Test',
      '-c',
      'user.email=test@invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      'candidate',
    ]);
    const targetCommit = execFileSync('git', ['-C', root, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
    const statementHash = '1'.repeat(64);
    const declarationHash = '2'.repeat(64);
    const contentSha256 = mathDigest(source);
    const verification = await verifyMathV2SourceCommit(
      {
        worktreePath: root,
        targetCommit,
        items: [
          {
            id: 'assignment:target',
            proofPath: sourcePath,
            contentSha256,
            theoremName: 'target',
            statementHash,
            expectedSourceDeclarationHash: declarationHash,
          },
        ],
      },
      async (): Promise<MathematicsVerifierBatchResult> => ({
        schema: 'deepscientist.mathematics.verification-batch/v1',
        sessionId: 'session',
        status: 'kernel_verified',
        targetCommit,
        startedAt: 1,
        checkedAt: 2,
        durationMs: 1,
        events: [],
        results: [
          {
            status: 'kernel_verified',
            targetCommit,
            statementHash,
            claim: 'statement',
            proofHash: contentSha256,
            proofPath: sourcePath,
            theoremName: 'target',
            sourceDeclarationHash: declarationHash,
            statementBinding: 'caller-bound-to-committed-declaration',
            toolchain: { lean: 'test' },
            verifier: 'lean-kernel',
            goalsRemaining: 0,
            sorryCount: 0,
            admitCount: 0,
            axioms: [],
            checkedAt: 2,
            checkId: 'assignment:target',
            receiptId: 'receipt',
            sessionId: 'session',
            ...overrides,
          },
        ],
      })
    );
    expect(verification.verified).toBe(false);
  });
});
