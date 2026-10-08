import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import {
  freezeMathRunInputs,
  verifyMathRunInputs,
  verifyMathRunInputsEnvironment,
  MATH_RUN_INPUTS_ENV,
  isMathLiteRunEnvironment,
  readMathRunInteractionProfile,
  readMathRunPlanningPolicy,
  readMathRunRetrievalCorpus,
} from '../src/math/mathRunInputs';
import {
  MATHEMATICS_INTERACTION_PROFILE_ENV,
  MATHEMATICS_LITE_INTERACTION_PROFILE,
  MATHEMATICS_PLANNING_POLICY_ENV,
  resolveMathematicsRuntimeEnvironment,
  mathematicsRuntimeInstruction,
} from '../src/math/mathRuntimeEnvironment';
import {
  createMathRetrievalCorpus,
  readMathRetrievalCorpusEnvironment,
  searchMathRetrievalCorpus,
} from '../src/math/mathRetrievalCorpus';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';

describe('frozen mathematics run input projection', () => {
  let parentDirectory: string;
  let workspace: string;
  const freeze = () =>
    freezeMathRunInputs({
      parentDirectory,
      workspace,
      task: 'Public task\n',
      environment: {
        PATH: '/pinned/bin',
        DEEPSCIENTIST_MATH_ENV_FILE: '/mutable/math.env',
        API_KEY: 'private-secret',
        EVALUATOR_COMMAND: 'private-evaluator',
      },
    });
  const retrievalFixture = async () => {
    fs.writeFileSync(path.join(workspace, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    fs.writeFileSync(
      path.join(workspace, 'lake-manifest.json'),
      JSON.stringify({
        packages: [{ name: 'Demo', type: 'git', url: 'https://github.com/example/demo', rev: 'frozen' }],
      })
    );
    fs.mkdirSync(path.join(workspace, '.lake/packages/Demo'), { recursive: true });
    const source = path.join(workspace, '.lake/packages/Demo/Main.lean');
    fs.writeFileSync(source, 'theorem fixture : True := by trivial\n');
    const original = path.join(parentDirectory, 'corpus.json');
    const content = canonicalMathJson(await createMathRetrievalCorpus(workspace, ['Demo']));
    fs.writeFileSync(original, content);
    const entry = path.join(parentDirectory, 'mcp.js');
    const implementation = 'console.log("fixture");\n';
    fs.writeFileSync(entry, implementation);
    return {
      source,
      original,
      entry,
      input: {
        parentDirectory,
        workspace,
        task: 'Public task',
        environment: {
          DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS: original,
          DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256: mathDigest(content),
        },
        retrievalImplementation: {
          path: entry,
          bytes: Buffer.byteLength(implementation),
          sha256: mathDigest(implementation),
        },
      },
    };
  };
  beforeEach(() => {
    parentDirectory = fs.mkdtempSync(path.join(os.tmpdir(), 'ds-frozen-math-'));
    workspace = path.join(parentDirectory, 'solver');
    fs.mkdirSync(workspace);
  });
  afterEach(() => {
    vi.restoreAllMocks();
    for (const entry of fs.readdirSync(parentDirectory, { withFileTypes: true })) {
      if (entry.isDirectory()) fs.chmodSync(path.join(parentDirectory, entry.name), 0o700);
    }
    fs.rmSync(parentDirectory, { recursive: true, force: true });
  });

  it('persists exact task bytes and only whitelisted environment settings', () => {
    const frozen = freeze();
    expect(verifyMathRunInputs(frozen.inputs)).toEqual(frozen.inputs);
    expect(frozen.inputs.task.digest).toBe(crypto.createHash('sha256').update('Public task\n').digest('hex'));
    expect(fs.readFileSync(frozen.inputs.environment.path, 'utf8')).not.toMatch(
      /private-secret|private-evaluator|mutable/
    );
  });

  it('selects lite behavior only from the immutable environment projection', () => {
    const frozen = freezeMathRunInputs({
      parentDirectory,
      workspace,
      task: 'Public task',
      environment: { [MATHEMATICS_INTERACTION_PROFILE_ENV]: MATHEMATICS_LITE_INTERACTION_PROFILE },
    });
    expect(readMathRunInteractionProfile(frozen.environment)).toBe(MATHEMATICS_LITE_INTERACTION_PROFILE);
    expect(isMathLiteRunEnvironment(frozen.environment)).toBe(true);
    expect(
      readMathRunInteractionProfile({
        ...freeze().environment,
        [MATHEMATICS_INTERACTION_PROFILE_ENV]: MATHEMATICS_LITE_INTERACTION_PROFILE,
      })
    ).toBeUndefined();
  });

  it('reads planning mode from frozen inputs, not inherited process overrides', () => {
    const key = MATHEMATICS_PLANNING_POLICY_ENV;
    const guided = freezeMathRunInputs({
      parentDirectory,
      workspace,
      task: 'Public task',
      environment: { [key]: 'failure-guided' },
    });
    expect(readMathRunPlanningPolicy({ ...guided.environment, [key]: 'current' })).toBe('failure-guided');
    const legacy = freezeMathRunInputs({
      parentDirectory,
      workspace,
      task: 'Another public task',
      environment: {},
    });
    expect(readMathRunPlanningPolicy({ ...legacy.environment, [key]: 'failure-guided' })).toBe('current');
  });

  it('copies retrieval identity into the immutable run and pins the runtime implementation', async () => {
    const { input, original, entry } = await retrievalFixture();
    const frozen = freezeMathRunInputs(input);
    fs.writeFileSync(original, 'operator changed the original manifest');
    expect(verifyMathRunInputs(frozen.inputs)).toEqual(frozen.inputs);
    expect(path.dirname(frozen.inputs.retrievalCorpus!.path)).toBe(frozen.inputs.root);
    expect(readMathRetrievalCorpusEnvironment(frozen.environment, entry)).toMatchObject({
      originSha256: input.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256,
      implementation: { sha256: input.retrievalImplementation.sha256 },
    });
  });

  it('uses the bound corpus despite inherited overrides and keeps legacy runs unfrozen', async () => {
    const { input, entry } = await retrievalFixture();
    const frozen = freezeMathRunInputs(input);
    expect(
      readMathRunRetrievalCorpus(
        { ...frozen.environment, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS: '/invalid/inherited' },
        entry
      )
    ).toEqual(readMathRetrievalCorpusEnvironment(frozen.environment, entry));
    expect(readMathRunRetrievalCorpus({ ...freeze().environment, ...input.environment }, entry)).toBeUndefined();
  });

  it('rejects corrupt corpus bytes and omission of its Core-held identity', async () => {
    const { input } = await retrievalFixture();
    const frozen = freezeMathRunInputs(input);
    const { retrievalCorpus, ...omitted } = frozen.inputs;
    expect(() => verifyMathRunInputs(omitted)).toThrow('Stop this run');
    fs.chmodSync(retrievalCorpus!.path, 0o600);
    fs.appendFileSync(retrievalCorpus!.path, ' ');
    fs.chmodSync(retrievalCorpus!.path, 0o400);
    expect(() => verifyMathRunInputs(frozen.inputs)).toThrow('Stop this run');
  });

  it('replays corpus paths relative to a nested Lean project without allowing an external project', async () => {
    const { input } = await retrievalFixture();
    const project = path.join(workspace, 'generated/public');
    fs.mkdirSync(project, { recursive: true });
    for (const name of ['lean-toolchain', 'lake-manifest.json', '.lake'])
      fs.renameSync(path.join(workspace, name), path.join(project, name));
    const frozen = freezeMathRunInputs({ ...input, retrievalProjectRoot: project });
    const corpus = readMathRetrievalCorpusEnvironment(frozen.environment);
    expect(searchMathRetrievalCorpus(workspace, corpus, ['fixture']).premises[0]?.sourceFile).toBe(
      'generated/public/.lake/packages/Demo/Main.lean'
    );
    expect(() => freezeMathRunInputs({ ...input, retrievalProjectRoot: parentDirectory })).toThrow(
      'math_corpus_project_path_invalid'
    );
  });

  it('rejects mismatched corpus sources or implementation before publishing run inputs', async () => {
    const { input, source, entry } = await retrievalFixture();
    const before = fs.readdirSync(parentDirectory);
    expect(() => freezeMathRunInputs({ ...input, retrievalImplementation: undefined })).toThrow(
      'math_corpus_implementation_missing'
    );
    fs.appendFileSync(source, '-- drift');
    expect(() => freezeMathRunInputs(input)).toThrow('math_corpus_source_changed');
    fs.appendFileSync(entry, '// drift');
    expect(() => freezeMathRunInputs(input)).toThrow('math_corpus_implementation_changed');
    expect(fs.readdirSync(parentDirectory)).toEqual(before);
  });

  it('rejects a different actual MCP entry and an environment rebound to the original corpus', async () => {
    const { input, entry } = await retrievalFixture();
    const frozen = freezeMathRunInputs(input);
    fs.appendFileSync(entry, '// changed implementation');
    expect(() => readMathRetrievalCorpusEnvironment(frozen.environment, entry)).toThrow(
      'math_corpus_implementation_changed'
    );
    fs.chmodSync(frozen.inputs.environment.path, 0o600);
    const env = { ...frozen.environment, ...input.environment };
    const contents = JSON.stringify(env);
    fs.writeFileSync(frozen.inputs.environment.path, contents);
    fs.chmodSync(frozen.inputs.environment.path, 0o400);
    expect(() =>
      verifyMathRunInputs({
        ...frozen.inputs,
        environment: { ...frozen.inputs.environment, bytes: Buffer.byteLength(contents), digest: mathDigest(contents) },
      })
    ).toThrow('Stop this run');
  });

  it('uses distinct run directories without rewriting earlier inputs', () => {
    const first = freeze();
    const second = freeze();
    expect(first.inputs.root).not.toBe(second.inputs.root);
    expect(verifyMathRunInputs(first.inputs)).toEqual(first.inputs);
  });

  it('does not reload mutable defaults or expand variable-looking frozen values', () => {
    const frozen = freezeMathRunInputs({
      parentDirectory,
      workspace,
      task: 'Task',
      environment: { PATH: '/literal/$PATH', LEAN_PATH: '/frozen/lib' },
    });
    const resolved = resolveMathematicsRuntimeEnvironment({
      ...frozen.environment,
      PATH: '/changed/bin',
      LEAN_PATH: '/changed/lib',
      ELAN_HOME: '/changed/elan',
      API_KEY: 'secret',
    });
    expect(resolved).toMatchObject({ PATH: '/literal/$PATH', LEAN_PATH: '/frozen/lib', ELAN_HOME: '' });
    expect(resolved.API_KEY).toBeUndefined();
    expect(mathematicsRuntimeInstruction(frozen.inputs.environment.path)).toContain('do not source JSON');
  });

  it.each(['task', 'environment'] as const)('rejects a writable %s file even if its bytes did not change', (field) => {
    const { inputs } = freeze();
    fs.chmodSync(inputs[field].path, 0o600);
    expect(() => verifyMathRunInputs(inputs)).toThrow('no longer read-only');
  });

  it.each(['task', 'environment'] as const)('rejects changed %s bytes even after restoring read-only mode', (field) => {
    const { inputs } = freeze();
    fs.chmodSync(inputs[field].path, 0o600);
    fs.writeFileSync(inputs[field].path, 'private-replacement');
    fs.chmodSync(inputs[field].path, 0o400);
    expect(() => verifyMathRunInputs(inputs)).toThrow('modified');
  });

  it('rejects a replacement inode with identical bytes', () => {
    const { inputs } = freeze();
    fs.chmodSync(inputs.root, 0o700);
    fs.renameSync(inputs.task.path, path.join(inputs.root, 'old-task'));
    fs.writeFileSync(inputs.task.path, 'Public task\n', { mode: 0o400 });
    fs.chmodSync(inputs.root, 0o500);
    expect(() => verifyMathRunInputs(inputs)).toThrow('modified');
  });

  it('rejects symlink substitutions without reading the target', () => {
    const { inputs } = freeze();
    fs.chmodSync(inputs.root, 0o700);
    fs.renameSync(inputs.task.path, path.join(inputs.root, 'original-task'));
    fs.symlinkSync(path.join(inputs.root, 'original-task'), inputs.task.path);
    fs.chmodSync(inputs.root, 0o500);
    expect(() => verifyMathRunInputs(inputs)).toThrow('modified');
  });

  it('rejects relocation through a compatibility link even when bytes and inode survive', () => {
    const { inputs } = freeze();
    const moved = `${inputs.root}-moved`;
    fs.renameSync(inputs.root, moved);
    fs.symlinkSync(moved, inputs.root);
    try {
      expect(fs.statSync(inputs.task.path).ino.toString()).toBe(inputs.task.inode);
      expect(() => verifyMathRunInputs(inputs)).toThrow('modified');
    } finally {
      fs.unlinkSync(inputs.root);
      fs.renameSync(moved, inputs.root);
    }
    expect(verifyMathRunInputs(inputs)).toEqual(inputs);
  });

  it('rejects hardlinks and writable projection directories', () => {
    const { inputs } = freeze();
    fs.linkSync(inputs.task.path, path.join(parentDirectory, 'task-link'));
    expect(() => verifyMathRunInputs(inputs)).toThrow('modified');
    fs.unlinkSync(path.join(parentDirectory, 'task-link'));
    fs.chmodSync(inputs.root, 0o700);
    expect(() => verifyMathRunInputs(inputs)).toThrow('no longer read-only');
  });

  it('fails closed for a missing projection instead of falling back to host settings', () => {
    expect(() =>
      resolveMathematicsRuntimeEnvironment({
        PATH: '/host/bin',
        DEEPSCIENTIST_MATH_ENV_FILE: path.join(parentDirectory, 'missing.json'),
      })
    ).toThrow();
  });

  it.each(['{}', '{"API_KEY":"private"}', 'private-invalid-json'])(
    'rejects incomplete or invalid frozen environment JSON',
    (content) => {
      const file = path.join(parentDirectory, 'invalid.json');
      fs.writeFileSync(file, content);
      expect(() => resolveMathematicsRuntimeEnvironment({ PATH: '/host', DEEPSCIENTIST_MATH_ENV_FILE: file })).toThrow(
        'Invalid mathematics environment projection'
      );
    }
  );

  it('checks Core-held metadata and the selected environment path without exposing corrupt data', () => {
    const frozen = freeze();
    expect(() => verifyMathRunInputsEnvironment(frozen.environment)).not.toThrow();
    expect(() =>
      verifyMathRunInputsEnvironment({ ...frozen.environment, DEEPSCIENTIST_MATH_ENV_FILE: '/different.json' })
    ).toThrow('modified');
    expect(() => verifyMathRunInputsEnvironment({ [MATH_RUN_INPUTS_ENV]: 'private-malformed-json' })).toThrow(
      'Stop this run'
    );
  });

  it('does not require new metadata for existing non-runner environments', () => {
    expect(() => verifyMathRunInputsEnvironment({})).not.toThrow();
  });

  it('removes only its unpublished directory when durable writing fails', () => {
    fs.writeFileSync(path.join(parentDirectory, 'keep'), 'existing');
    vi.spyOn(fs, 'fsyncSync').mockImplementation(() => {
      throw new Error('disk sync failed');
    });
    expect(freeze).toThrow('disk sync failed');
    expect(fs.readdirSync(parentDirectory).toSorted()).toEqual(['keep', 'solver']);
  });

  it('rejects empty tasks before creating any files', () => {
    expect(() => freezeMathRunInputs({ parentDirectory, workspace, task: '  ', environment: {} })).toThrow('empty');
    expect(fs.readdirSync(parentDirectory)).toEqual(['solver']);
  });

  it('rejects a projection directory inside the solver Git workspace', () => {
    expect(() => freezeMathRunInputs({ parentDirectory: workspace, workspace, task: 'Task', environment: {} })).toThrow(
      'outside the solver'
    );
    expect(fs.readdirSync(workspace)).toEqual([]);
  });
});
