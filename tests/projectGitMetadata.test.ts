import { describe, expect, it } from 'vitest';
import { parseGitLog } from '../src/project-git/projectGitParsers';
import { requiresResearchStrategyForCheckpoint } from '../src/common/chat/projectWorkspace';

describe('checkpoint metadata compatibility', () => {
  it('preserves mathematical strategy and historical domain metadata', () => {
    const log = [
      ['a'.repeat(40), 'aaaaaaa', '', '[deepen] Prove the lemma',
        'DeepScientist-Checkpoint: true\nDeepScientist-Domain: mathematics\nDeepScientist-Stage: proof\nDeepScientist-Strategy: deepen'],
      ['b'.repeat(40), 'bbbbbbb', '', 'Historical checkpoint',
        'DeepScientist-Checkpoint: true\nDeepScientist-Domain: financial_factor\nDeepScientist-Stage: report'],
      ['c'.repeat(40), 'ccccccc', '', 'Historical discovery checkpoint',
        'DeepScientist-Checkpoint: true\nDeepScientist-Domain: target_discovery\nDeepScientist-TargetSummary: {"candidateCount":2,"topTargets":["old-target"]}'],
    ].map(fields => fields.join('\x1f')).join('\x1e');
    const commits = parseGitLog(log);
    expect(commits[0].checkpoint).toMatchObject({ domain: 'mathematics', stage: 'proof', researchStrategy: 'deepen' });
    expect(commits[1].checkpoint).toMatchObject({ domain: 'financial_factor', stage: 'report' });
    expect(commits[2].checkpoint).toMatchObject({ domain: 'target_discovery',
      targetSummary: { candidateCount: 2, topTargets: ['old-target'] } });
    expect(requiresResearchStrategyForCheckpoint('mathematics', 'proof')).toBe(true);
    expect(requiresResearchStrategyForCheckpoint('mathematics', 'report')).toBe(false);
  });
});
