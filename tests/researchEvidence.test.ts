import { expect, it } from 'vitest';
import { checkpointCandidate } from '../src/solver/researchEvidence';
import type { DeliveryArtifactManifest } from '../src/solver/deliveryArtifacts';

const notes = (summary: string, evidenceRefs = ['saved-experiment']) => JSON.stringify({ summary, evidenceRefs, conclusion: 'inconclusive' });
const artifact = (sha256 = 'code', offset = 1): DeliveryArtifactManifest => ({
  schema: 'theorem-os.delivery-artifacts.v1', scope: 'advisory-unverified', problemReceiptDigest: 'problem', taskId: 'task',
  taskDigest: 'version', seedCommit: 'seed', commit: `commit-${offset}`, artifacts: [{ id: `artifact-${offset}`, kind: 'notes-lean',
    file: 'RESEARCH.md', fileSha256: `notes-${offset}`, sha256, bytes: 100, startOffset: offset, endOffset: offset + 100,
    declarations: [{ name: 'candidate', header: 'lemma candidate : True', sha256, draft: true }] }],
});

it('does not turn a rephrased summary or moved code block into a new candidate', () => {
  const first = checkpointCandidate(notes('Try this calculation.'), artifact());
  expect(first.status).toBe('structured-candidate');
  expect(checkpointCandidate(notes('The same calculation, rewritten.'), artifact('code', 300))).toEqual(first);
  expect(checkpointCandidate(notes('New code'), artifact('different-code')).digest).not.toBe(first.digest);
  expect(checkpointCandidate(notes('A new experiment', ['new-experiment']), artifact()).digest).not.toBe(first.digest);
});

it('keeps prose and incomplete structured notes unclassified without rejecting the draft', () => {
  const first = checkpointCandidate('A long mathematical argument with a new intermediate calculation.');
  expect(first.status).toBe('unclassified-draft');
  expect(checkpointCandidate('An alternative proof calculation.')).toEqual(first);
  expect(() => checkpointCandidate('{"summary": "unfinished')).not.toThrow();
  expect(checkpointCandidate('{"summary": "unfinished').status).toBe('unclassified-draft');
});

it('tracks negative findings and exact proposals without using their explanatory prose as identity', () => {
  const response = { summary: 'A local counterexample', conclusion: 'refuted',
    blockers: [{ blockerId: 'blocker_123', mechanism: 'first phrasing', scope: 'local step' }],
    lemmaRequests: [{ id: 'bridge', kind: 'lemma', objective: 'first explanation', theoremName: 'bridge', type: 'True',
      proofPath: 'Submission.lean', dependsOn: [], revision: 0 }] };
  const first = checkpointCandidate(JSON.stringify(response));
  expect(first.status).toBe('structured-candidate');
  response.summary = 'The same negative finding';
  response.blockers[0].mechanism = 'another explanation';
  response.lemmaRequests[0].objective = 'another explanation';
  response.lemmaRequests[0].revision = 10;
  expect(checkpointCandidate(JSON.stringify(response))).toEqual(first);
  response.lemmaRequests[0].type = 'False';
  expect(checkpointCandidate(JSON.stringify(response)).digest).not.toBe(first.digest);
});
