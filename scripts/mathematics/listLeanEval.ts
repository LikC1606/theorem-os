#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import { fetchLeanEvalLeaderboardCredits, readLeanEvalCatalog } from '../../src/math/leanEvalCatalogAdapter';
import { resolveMathematicsRuntimeEnvironment } from '../../src/math/mathRuntimeEnvironment';

async function main() {
  const { values } = parseArgs({ options: { repo: { type: 'string' }, problem: { type: 'string' },
    limit: { type: 'string', default: '10' }, leaderboard: { type: 'boolean' }, help: { type: 'boolean' } } });
  if (values.help) {
    console.log('Usage: theorem-os list-lean-eval [--repo DIR] [--problem ID] [--limit N] [--leaderboard]\nLists active V1 public obligations and formalization gap warnings. Library coverage needs review; model credits are only an auxiliary signal.');
    return;
  }
  const repositoryRoot = values.repo || resolveMathematicsRuntimeEnvironment().DEEPSCIENTIST_LEAN_EVAL_ROOT;
  if (!repositoryRoot) throw new Error('--repo is required');
  const limit = Number(values.limit);
  if (!Number.isSafeInteger(limit) || limit < 1) throw new Error('--limit must be a positive integer');
  const leaderboard = values.leaderboard ? await fetchLeanEvalLeaderboardCredits() : undefined;
  const catalog = readLeanEvalCatalog({ repositoryRoot, verifyGitCommit: true, credits: leaderboard?.credits });
  const candidates = catalog.problems.filter(problem => problem.activeV1 && problem.visible && problem.status === 'active' &&
    (!values.problem || values.problem === problem.id));
  if (values.problem && !candidates.length) throw new Error('No active V1 problem matches --problem');
  console.log(JSON.stringify({ benchmarkCommit: catalog.benchmarkCommit, catalogHash: catalog.catalogHash,
    total: candidates.length, selectionNote: 'Review the core obligations and library coverage before choosing. Public warnings are authors’ claims; absence of a warning does not establish library coverage or low difficulty.',
    problems: candidates.toSorted((a, b) => Number(Boolean(a.selectionEvidence?.publicGapNotes.length)) -
      Number(Boolean(b.selectionEvidence?.publicGapNotes.length)) || a.id.localeCompare(b.id)).slice(0, limit)
      .map(problem => ({ id: problem.id, title: problem.title, obligations: problem.holes,
        acceptedModels: leaderboard ? problem.acceptedModelIds.length : null,
        selectionEvidence: problem.selectionEvidence })) }, null, 2));
}
main().catch(error => { console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1; });
