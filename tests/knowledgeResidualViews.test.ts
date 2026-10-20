import { expect, it } from 'vitest';
import { knowledgeResidualViews } from '../src/solver/theoremKnowledgeGoal';
import { searchTheoremKnowledge } from '../src/solver/theoremKnowledgeSearch';
import type { TheoremKnowledgeEntry } from '../src/solver/theoremKnowledge';

const base = { evidence: 'recorded-not-replayed' as const, entries: [{ id: 'comm', name: 'Saved.comm',
  type: '∀ (a b : ℝ), a + b = b + a', typeKind: 'closed-task-type', description: '', premises: [], provenance: [],
  dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' } } as unknown as TheoremKnowledgeEntry] };

it.each(['x y', 'left right'])('recalls a closed theorem for alpha-renamed residual locals %s', names => {
  const [a, b] = names.split(' '), goal = `${names} : ℝ\n⊢ ${a} + ${b} = ${b} + ${a}`;
  expect(searchTheoremKnowledge(base, '', { goal }).hits.map(hit => hit.id)).toEqual(['comm']);
  expect(knowledgeResidualViews(goal)[0]).toMatchObject({ goal: `∀ (${names} : ℝ), ${a} + ${b} = ${b} + ${a}`,
    localContext: 'closed-for-retrieval' });
});

it('keeps hypotheses private to each displayed case and conservatively falls back for local definitions', () => {
  const views = knowledgeResidualViews('case left\nx : ℝ\nh : x > 0\n⊢ x = x\n\ncase right\ny : Nat := 3\n⊢ Nat.Prime y');
  expect(views[0]).toMatchObject({ caseLabel: 'left', goal: '∀ (x : ℝ) (h : x > 0), x = x' });
  expect(views[1]).toMatchObject({ caseLabel: 'right', goal: 'Nat.Prime y', localContext: 'target-only',
    fallbackReason: 'unsupported-local-declaration' });
  expect(views[1]!.goal).not.toContain('x > 0');
});

it('does not manufacture lexical hits from unrelated local hypotheses', () => {
  expect(searchTheoremKnowledge(base, '', { goal: 'h : ∀ (a b : ℝ), a + b = b + a\n⊢ UnavailableTarget' }).hits).toEqual([]);
});
