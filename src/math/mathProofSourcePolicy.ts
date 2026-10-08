/** Candidate proofs may use Submission.lean; reference and evaluator trees are not construction inputs. */
const excludedSegments = new Set([
  '.git',
  '.lake',
  'bench',
  'benchmark',
  'benchmarks',
  'build',
  'example',
  'examples',
  'lakefile',
  'private',
  'reference',
  'references',
  'solution',
  'solutions',
  'workspacetest',
  'test',
  'tests',
  'comparator',
  'comparators',
  'challenge',
  'challenges',
]);

export function isAllowedMathProofSource(relative: string): boolean {
  const normalized = relative.replaceAll('\\', '/');
  return (
    normalized.endsWith('.lean') &&
    !normalized.startsWith('/') &&
    !/^[A-Za-z]:/u.test(normalized) &&
    normalized
      .split('/')
      .every(
        (part) =>
          Boolean(part) &&
          part !== '.' &&
          part !== '..' &&
          !excludedSegments.has(part.replace(/\.lean$/iu, '').toLowerCase())
      )
  );
}
