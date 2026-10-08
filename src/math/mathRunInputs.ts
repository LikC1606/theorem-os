/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { projectMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import {
  MATHEMATICS_INTERACTION_PROFILE_ENV,
  MATHEMATICS_LITE_INTERACTION_PROFILE,
  MATHEMATICS_SECOND_PROOF_OWNER_ENV,
  MATHEMATICS_PLANNING_POLICY_ENV,
  parseMathematicsPlanningPolicy,
  type MathematicsPlanningPolicy,
} from "./mathRuntimeEnvironment";
import {
  MATH_RETRIEVAL_CORPUS_ENV,
  MATH_RETRIEVAL_CORPUS_SHA_ENV,
  readMathRetrievalCorpusEnvironment,
  verifyMathRetrievalCorpus,
  verifyMathRetrievalImplementation,
} from "./mathRetrievalCorpus";
import { canonicalMathJson } from "./mathRuntimeIo";
import type { MathRunBinding } from "../common/types/team/mathRuntimeContracts";

export const MATH_RUN_INPUTS_ENV = 'DEEPSCIENTIST_MATH_RUN_INPUTS';

const fileIdentity = z
  .object({
    path: z.string().min(1),
    digest: z.string().regex(/^[0-9a-f]{64}$/u),
    bytes: z.number().int().nonnegative().safe(),
    device: z.string().regex(/^\d+$/u),
    inode: z.string().regex(/^\d+$/u),
  })
  .strict();
const projectionSchema = z
  .object({
    root: z.string().min(1),
    task: fileIdentity,
    environment: fileIdentity,
    binding: fileIdentity.optional(),
    retrievalCorpus: fileIdentity.optional(),
  })
  .strict();
export type MathRunInputs = Readonly<z.infer<typeof projectionSchema>>;

const digest = (content: Uint8Array): string => crypto.createHash('sha256').update(content).digest('hex');
export class MathRunInputsIntegrityError extends Error {
  constructor() {
    super(
      'Mathematics run inputs are missing, modified, or no longer read-only. Stop this run; model edits cannot repair its identity.'
    );
    this.name = 'MathRunInputsIntegrityError';
  }
}
const invalid = (): Error => new MathRunInputsIntegrityError();

function readProjectionFile(file: z.infer<typeof fileIdentity>, root: string): Buffer {
  if (path.dirname(file.path) !== root || fs.realpathSync(file.path) !== file.path) throw invalid();
  const descriptor = fs.openSync(file.path, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(descriptor, { bigint: true });
    if (
      !before.isFile() ||
      before.nlink !== BigInt(1) ||
      before.size !== BigInt(file.bytes) ||
      (before.mode & BigInt(0o222)) !== BigInt(0) ||
      String(before.dev) !== file.device ||
      String(before.ino) !== file.inode
    )
      throw invalid();
    const content = fs.readFileSync(descriptor);
    const after = fs.fstatSync(descriptor, { bigint: true });
    const current = fs.lstatSync(file.path, { bigint: true });
    if (
      after.size !== before.size ||
      after.mtimeNs !== before.mtimeNs ||
      after.ctimeNs !== before.ctimeNs ||
      current.dev !== before.dev ||
      current.ino !== before.ino ||
      current.mode !== before.mode ||
      digest(content) !== file.digest ||
      fs.realpathSync(file.path) !== file.path
    )
      throw invalid();
    return content;
  } finally {
    fs.closeSync(descriptor);
  }
}

/** Metadata is held by runner/Core, never read back from a model-writable manifest. */
type VerifyMathRunInputsOptions = Readonly<{ allowWritableRoot?: boolean }>;

export function verifyMathRunInputs(value: unknown, options: VerifyMathRunInputsOptions = {}): MathRunInputs {
  try {
    const input = projectionSchema.parse(value);
    if (!path.isAbsolute(input.root) || fs.realpathSync(input.root) !== input.root) throw invalid();
    const stat = fs.lstatSync(input.root);
    if (
      !stat.isDirectory() ||
      (!options.allowWritableRoot && (stat.mode & 0o222) !== 0) ||
      input.task.path === input.environment.path
    )
      throw invalid();
    readProjectionFile(input.task, input.root);
    const environment = JSON.parse(
      new TextDecoder('utf-8', { fatal: true }).decode(readProjectionFile(input.environment, input.root))
    );
    if (!environment || typeof environment !== 'object' || Array.isArray(environment)) throw invalid();
    if (input.retrievalCorpus) {
      if (
        input.retrievalCorpus.path === input.task.path ||
        input.retrievalCorpus.path === input.environment.path ||
        input.retrievalCorpus.path === input.binding?.path
      )
        throw invalid();
      readProjectionFile(input.retrievalCorpus, input.root);
      if (
        environment[MATH_RETRIEVAL_CORPUS_ENV] !== input.retrievalCorpus.path ||
        environment[MATH_RETRIEVAL_CORPUS_SHA_ENV] !== input.retrievalCorpus.digest
      )
        throw invalid();
    } else if (
      environment[MATH_RETRIEVAL_CORPUS_ENV] !== undefined ||
      environment[MATH_RETRIEVAL_CORPUS_SHA_ENV] !== undefined
    )
      throw invalid();
    if (input.binding) {
      if (input.binding.path === input.task.path || input.binding.path === input.environment.path) throw invalid();
      readProjectionFile(input.binding, input.root);
    }
    return input;
  } catch {
    throw invalid();
  }
}

export function readMathRunBindingProjection(value: unknown): unknown {
  const inputs = verifyMathRunInputs(value);
  if (!inputs.binding) throw invalid();
  try {
    return JSON.parse(readProjectionFile(inputs.binding, inputs.root).toString('utf8'));
  } catch {
    throw invalid();
  }
}

export function readMathRunEnvironmentProjection(value: unknown, options: VerifyMathRunInputsOptions = {}): unknown {
  const inputs = verifyMathRunInputs(value, options);
  try {
    return JSON.parse(
      new TextDecoder('utf-8', { fatal: true }).decode(readProjectionFile(inputs.environment, inputs.root))
    );
  } catch {
    throw invalid();
  }
}

export function verifyMathRunInputsEnvironment(env: NodeJS.ProcessEnv): void {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (encoded === undefined) return;
  try {
    const inputs = verifyMathRunInputs(JSON.parse(encoded));
    if (env.DEEPSCIENTIST_MATH_ENV_FILE !== inputs.environment.path) throw invalid();
  } catch {
    throw invalid();
  }
}

/** Read the interaction contract only from the immutable run projection. */
export function readMathRunInteractionProfile(env: NodeJS.ProcessEnv): string | undefined {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (encoded === undefined) return undefined;
  verifyMathRunInputsEnvironment(env);
  const environment = z.record(z.string(), z.string()).parse(readMathRunEnvironmentProjection(JSON.parse(encoded)));
  return environment[MATHEMATICS_INTERACTION_PROFILE_ENV];
}

/** Only the frozen run inputs can enable a second proof owner; live env cannot. */
export function readMathRunSecondProofOwner(env: NodeJS.ProcessEnv): boolean {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (encoded === undefined) return false;
  verifyMathRunInputsEnvironment(env);
  const environment = z.record(z.string(), z.string()).parse(readMathRunEnvironmentProjection(JSON.parse(encoded)));
  return environment[MATHEMATICS_SECOND_PROOF_OWNER_ENV] === 'true';
}

/** Legacy frozen runs have the current policy; live process env cannot override it. */
export function readMathRunPlanningPolicy(env: NodeJS.ProcessEnv): MathematicsPlanningPolicy {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (encoded === undefined) return 'current';
  verifyMathRunInputsEnvironment(env);
  const environment = z.record(z.string(), z.string()).parse(readMathRunEnvironmentProjection(JSON.parse(encoded)));
  return parseMathematicsPlanningPolicy(environment[MATHEMATICS_PLANNING_POLICY_ENV]);
}

export function isMathLiteRunEnvironment(env: NodeJS.ProcessEnv): boolean {
  return readMathRunInteractionProfile(env) === MATHEMATICS_LITE_INTERACTION_PROFILE;
}

/** A managed MCP reads the Core-held projection, never an inherited policy override. */
export function readMathRunRetrievalCorpus(env: NodeJS.ProcessEnv, runtimeEntry: string) {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (encoded === undefined) return readMathRetrievalCorpusEnvironment(env, runtimeEntry);
  verifyMathRunInputsEnvironment(env);
  const environment = z.record(z.string(), z.string()).parse(readMathRunEnvironmentProjection(JSON.parse(encoded)));
  return readMathRetrievalCorpusEnvironment(environment, runtimeEntry);
}

/** Retained with the run receipt; never deletes or overwrites a previous run's files. */
export function freezeMathRunInputs(
  input: Readonly<{
    parentDirectory: string;
    workspace: string;
    task: string;
    environment: NodeJS.ProcessEnv;
    retrievalImplementation?: Readonly<{ path: string; sha256: string; bytes: number }>;
    retrievalProjectRoot?: string;
    createBinding?: (inputs: MathRunInputs) => MathRunBinding;
  }>
): Readonly<{ inputs: MathRunInputs; environment: NodeJS.ProcessEnv }> {
  if (!input.task.trim()) throw new Error('Public task is empty');
  let corpus = readMathRetrievalCorpusEnvironment(input.environment);
  if (corpus) {
    if (!input.retrievalImplementation) throw new Error('math_corpus_implementation_missing');
    const subdirectory = path.relative(
      fs.realpathSync(input.workspace),
      fs.realpathSync(input.retrievalProjectRoot ?? input.workspace)
    );
    if (subdirectory === '..' || subdirectory.startsWith(`..${path.sep}`) || path.isAbsolute(subdirectory))
      throw new Error('math_corpus_project_path_invalid');
    const projectSubdirectory = subdirectory ? subdirectory.replaceAll(path.sep, '/') : undefined;
    if (corpus.projectSubdirectory && corpus.projectSubdirectory !== projectSubdirectory)
      throw new Error('math_corpus_project_path_invalid');
    corpus = { ...corpus, ...(projectSubdirectory ? { projectSubdirectory } : {}) };
    verifyMathRetrievalImplementation(input.retrievalImplementation.path, input.retrievalImplementation);
    verifyMathRetrievalCorpus(input.workspace, corpus);
  }
  fs.mkdirSync(input.parentDirectory, { recursive: true });
  const parent = fs.realpathSync(input.parentDirectory);
  const relative = path.relative(fs.realpathSync(input.workspace), parent);
  if (!relative || (!path.isAbsolute(relative) && relative !== '..' && !relative.startsWith(`..${path.sep}`))) {
    throw new Error('Mathematics run inputs must be outside the solver workspace');
  }
  const root = fs.mkdtempSync(path.join(parent, '.math-run-inputs-'));
  try {
    fs.chmodSync(root, 0o700);
    const environmentPath = path.join(root, 'environment.json');
    const environment: Record<string, string> = {
      ...projectMathematicsRuntimeEnvironment(input.environment),
      DEEPSCIENTIST_MATH_ENV_FILE: environmentPath,
    };
    const write = (name: string, content: string) => {
      const file = path.join(root, name);
      const descriptor = fs.openSync(file, 'wx', 0o600);
      try {
        fs.writeFileSync(descriptor, content, 'utf8');
        fs.fchmodSync(descriptor, 0o400);
        fs.fsyncSync(descriptor);
        const stat = fs.fstatSync(descriptor, { bigint: true });
        return Object.freeze({
          path: file,
          digest: digest(Buffer.from(content, 'utf8')),
          bytes: Buffer.byteLength(content, 'utf8'),
          device: String(stat.dev),
          inode: String(stat.ino),
        });
      } finally {
        fs.closeSync(descriptor);
      }
    };
    const retrievalCorpus =
      corpus && input.retrievalImplementation
        ? write(
            'retrieval-corpus.json',
            canonicalMathJson({
              ...corpus,
              originSha256: input.environment[MATH_RETRIEVAL_CORPUS_SHA_ENV],
              implementation: {
                sha256: input.retrievalImplementation.sha256,
                bytes: input.retrievalImplementation.bytes,
              },
            })
          )
        : undefined;
    if (retrievalCorpus) {
      environment[MATH_RETRIEVAL_CORPUS_ENV] = retrievalCorpus.path;
      environment[MATH_RETRIEVAL_CORPUS_SHA_ENV] = retrievalCorpus.digest;
    }
    const task = write('task.md', input.task);
    const environmentFile = write('environment.json', JSON.stringify(environment));
    const binding = input.createBinding
      ? write(
          'binding.json',
          JSON.stringify(
            input.createBinding({
              root,
              task,
              environment: environmentFile,
              ...(retrievalCorpus ? { retrievalCorpus } : {}),
            })
          )
        )
      : undefined;
    fs.chmodSync(root, 0o500);
    for (const directory of [root, path.dirname(root)]) {
      const descriptor = fs.openSync(directory, 'r');
      try {
        fs.fsyncSync(descriptor);
      } finally {
        fs.closeSync(descriptor);
      }
    }
    const inputs = Object.freeze({
      root,
      task,
      environment: environmentFile,
      ...(binding ? { binding } : {}),
      ...(retrievalCorpus ? { retrievalCorpus } : {}),
    });
    verifyMathRunInputs(inputs);
    return Object.freeze({
      inputs,
      environment: Object.freeze({ ...environment, [MATH_RUN_INPUTS_ENV]: JSON.stringify(inputs) }),
    });
  } catch (error) {
    fs.chmodSync(root, 0o700);
    fs.rmSync(root, { recursive: true, force: true });
    throw error;
  }
}
