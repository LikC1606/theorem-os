import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { it, expect } from 'vitest';
import { readLeanEvalCatalog } from '../src/math/leanEvalCatalogAdapter';

it('surfaces public formalization gaps without treating model credits or silence as library coverage', () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-eval-selection-'));
  try {
    for (const folder of ['manifests/sets', 'manifests/problems', 'generated/p']) fs.mkdirSync(path.join(root, folder), { recursive: true });
    fs.writeFileSync(path.join(root, 'generated/index.json'), JSON.stringify([{ id: 'p', generated_path: 'generated/p' }]));
    fs.writeFileSync(path.join(root, 'manifests/sets/v1.toml'), '[[members]]\nproblem_id = "p"\nstatement_revision = 1\n');
    fs.writeFileSync(path.join(root, 'manifests/problems/p.toml'), 'status = "active"\nvisible = true\n');
    fs.writeFileSync(path.join(root, 'generated/p/holes.json'), JSON.stringify({ id: 'p', holes: [{ name: 'full', kind: 'theorem' }] }));
    const file = path.join(root, 'generated/p/ChallengeDeps.lean');
    fs.writeFileSync(file, '/- mathlib has Roth but **not** the full theorem.\nAn open formalization target. -/\n');
    const credits = [{ problemId: 'p', statementRevision: 1, canonicalModelId: 'model' }];
    const catalog = readLeanEvalCatalog({ repositoryRoot: root, credits });
    expect(catalog.problems[0].selectionEvidence).toMatchObject({ libraryReview: 'unreviewed',
      publicGapNotes: [expect.objectContaining({ file: 'generated/p/ChallengeDeps.lean', text: expect.stringContaining('open formalization target') })] });
    expect(catalog.problems[0].acceptedModelIds).toEqual(['model']);
    fs.writeFileSync(file, '-- no explicit coverage claim\n');
    const next = readLeanEvalCatalog({ repositoryRoot: root, credits });
    expect(next.problems[0].selectionEvidence).toMatchObject({ libraryReview: 'unreviewed', publicGapNotes: [] });
    expect(next.catalogHash).not.toBe(catalog.catalogHash);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});
