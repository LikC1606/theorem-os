import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { z } from 'zod';
import {
  mathRouteStructureSignatureFromNormalized,
  normalizeMathRouteCard,
  isMathFoundationalLeanAxiom,
  type MathRouteCard,
} from "../common/types/team/mathematicsTeam";
import { inspectLeanDeclarations, runFormalVerification, type MathematicsVerifierExecutionOptions } from "./verifier";
import { canonicalMathJson } from "./mathRuntimeIo";
import { readMathematicsReceiptSecret } from "./receiptAttestation";
import { readMathRunHistoryIdentity } from "./mathRunHistory";
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";

const digest = (value: string) => crypto.createHash('sha256').update(value).digest('hex');
const prefix = 'math-route-refutation:';
const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const receiptSchema = z
  .object({
    schema: z.literal('deepscientist.math.route-refutation.v1'),
    runIdentity: z.string().min(1),
    teamId: z.string().min(1),
    assignmentId: z.string().min(1),
    statementHash: hash,
    routeFingerprint: z.string().min(1),
    structureSignature: hash,
    planNodeId: z.string().min(1),
    obligationDeclarationDigest: hash,
    obligationSourceHash: hash,
    expectedTypeDigest: hash,
    proofHash: hash,
    theoremDeclarationHash: hash,
    targetCommit: z.string().min(1),
    baseCommit: z.string().min(1),
    verificationCommit: z.string().min(1),
    proofPath: z.string().min(1),
    theoremName: z.string().min(1),
  })
  .strict();

/** This binding must come from the durable original assignment, never a worker tool argument. */
export type MathRouteRefutationBinding = Readonly<{
  teamId: string;
  assignmentId: string;
  routeCard: MathRouteCard;
  baseCommit: string;
}>;

function closedProposition(header: string, name: string): string {
  const signature = header.slice(name.length).trim();
  const stack: string[] = [];
  const closing: Record<string, string> = { '(': ')', '[': ']', '{': '}' };
  let quoted = false;
  for (let index = 0; index < signature.length; index++) {
    const char = signature[index]!;
    if (quoted) {
      if (char === '\\') index++;
      else if (char === '"') quoted = false;
      continue;
    }
    if (char === '"') quoted = true;
    else if (closing[char]) stack.push(closing[char]!);
    else if ([')', ']', '}'].includes(char)) {
      if (stack.pop() !== char) throw new Error('Invalid route obligation delimiters');
    } else if (char === ':' && !stack.length) {
      const binders = signature.slice(0, index).trim();
      const conclusion = signature.slice(index + 1).trim();
      if (!conclusion || (binders && !['(', '[', '{'].includes(binders[0]!))) break;
      return binders ? `(forall ${binders}, ${conclusion})` : `(${conclusion})`;
    }
  }
  throw new Error('Route obligation requires an explicitly typed closed theorem declaration');
}

export function prepareMathRouteRefutationTarget(input: MathRouteRefutationBinding & { planNodeId: string }) {
  if (!/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u.test(input.baseCommit))
    throw new Error('Route refutation requires the original base commit');
  const card = normalizeMathRouteCard(input.routeCard);
  const nodes = new Map(card.planNodes.map((node) => [node.id, node]));
  const children = new Map<string, string[]>();
  for (const node of card.planNodes) {
    if (node.parentNodeId) children.set(node.parentNodeId, [...(children.get(node.parentNodeId) ?? []), node.id]);
  }
  const required = new Set<string>();
  const visit = (id: string) => {
    if (required.has(id)) return;
    const node = nodes.get(id);
    if (!node) throw new Error('Route obligation dependency is missing');
    required.add(id);
    node.dependsOn.forEach(visit);
    // Original containment children must all complete before their parent is actionable.
    // Only the durable original card supplies these edges, never a worker's later expansion.
    (children.get(id) ?? []).forEach(visit);
  };
  visit(card.rootNodeId);
  const node = nodes.get(input.planNodeId);
  if (!node || !required.has(node.id)) throw new Error('Refutation must target a necessary original route node');
  const source = node.provisionalLeanStatement;
  const parsed = inspectLeanDeclarations(source);
  const declarations = parsed.length ? parsed : inspectLeanDeclarations(`${source} := by sorry`);
  if (declarations.length !== 1 || declarations[0]!.kind !== 'theorem')
    throw new Error('Route refutation requires one theorem obligation');
  const declaration = declarations[0]!;
  const expectedDeclarationType = `_root_.Not ${closedProposition(declaration.declarationType, declaration.name)}`;
  return Object.freeze({
    teamId: input.teamId,
    assignmentId: input.assignmentId,
    baseCommit: input.baseCommit,
    statementHash: card.statementHash,
    routeFingerprint: card.routeFingerprint,
    structureSignature: digest(mathRouteStructureSignatureFromNormalized(card)),
    planNodeId: node.id,
    obligationDeclarationDigest: digest(declaration.declarationType),
    obligationSourceHash: digest(source),
    expectedTypeDigest: digest(expectedDeclarationType),
    expectedDeclarationType,
  });
}

/** Mask comments and string text while preserving code inside Lean string interpolations. */
export function mathRefutationCommandSurface(source: string): string {
  const output = source.split('');
  let index = 0;
  const mask = () => {
    if (output[index] !== '\n') output[index] = ' ';
    index++;
  };
  const code = (interpolation = false): void => {
    let braces = 0;
    while (index < source.length) {
      if (source.startsWith('--', index)) {
        while (index < source.length && source[index] !== '\n') mask();
      } else if (source.startsWith('/-', index)) {
        let depth = 1;
        mask();
        mask();
        while (index < source.length && depth) {
          if (source.startsWith('/-', index)) {
            depth++;
            mask();
            mask();
          } else if (source.startsWith('-/', index)) {
            depth--;
            mask();
            mask();
          } else mask();
        }
      } else if (source[index] === 'r' && /^r#+"/u.test(source.slice(index))) {
        const prefix = /^r(#+)"/u.exec(source.slice(index))!;
        const closing = `"${prefix[1]}`;
        const end = source.indexOf(closing, index + prefix[0].length);
        const until = end < 0 ? source.length : end + closing.length;
        while (index < until) mask();
      } else if (source[index] === "'" && /^'(?:\\.|[^'\\])'/u.test(source.slice(index))) {
        const literal = /^'(?:\\.|[^'\\])'/u.exec(source.slice(index))![0];
        const end = index + literal.length;
        while (index < end) mask();
      } else if (source[index] === '"') {
        const interpolated = source[index - 1] === '!';
        mask();
        while (index < source.length) {
          if (source[index] === '\\') {
            mask();
            if (index < source.length) mask();
          } else if (source[index] === '"') {
            mask();
            break;
          } else if (interpolated && source[index] === '{') {
            if (source[index + 1] === '{') {
              mask();
              mask();
            } else {
              mask();
              code(true);
            }
          } else mask();
        }
      } else if (interpolation && source[index] === '}' && braces === 0) {
        mask();
        return;
      } else {
        if (source[index] === '{') braces++;
        if (source[index] === '}') braces--;
        index++;
      }
    }
  };
  code();
  return output.join('');
}

function isolateProof(
  input: MathRouteRefutationBinding & {
    projectRoot: string;
    targetCommit: string;
    proofPath: string;
    theoremName: string;
  }
) {
  if (!/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u.test(input.targetCommit) || !isAllowedMathProofSource(input.proofPath))
    throw new Error('Route refutation requires a committed construction proof');
  const git = (root: string, ...args: string[]) =>
    execFileSync('git', ['-C', root, ...args], { encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 });
  const tree = git(input.projectRoot, 'ls-tree', input.targetCommit, '--', input.proofPath);
  if (!/^100(?:644|755) blob /u.test(tree)) throw new Error('Route refutation proof must be a committed regular file');
  if (git(input.projectRoot, 'ls-tree', input.baseCommit, '--', input.proofPath).trim())
    throw new Error('Route refutation requires a new dedicated proof file, preserving the original context');
  const source = git(input.projectRoot, 'show', `${input.targetCommit}:${input.proofPath}`);
  const declarations = inspectLeanDeclarations(source);
  // The proof may use the original environment, but cannot extend its parser or inject commands.
  if (
    declarations.length !== 1 ||
    declarations[0]!.kind !== 'theorem' ||
    declarations[0]!.name !== input.theoremName ||
    /\b(?:macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|axiom|opaque|instance|attribute|set_option|run_cmd|run_tac|by_elab|unsafe|initialize|builtin_initialize)\b|#/u.test(
      mathRefutationCommandSurface(source)
    )
  )
    throw new Error('Route refutation file must contain one theorem without environment extensions');
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-route-refutation-verify-'));
  try {
    execFileSync(
      'git',
      ['clone', '--quiet', '--no-checkout', '--shared', '--', path.resolve(input.projectRoot), root],
      { stdio: 'pipe' }
    );
    git(root, 'checkout', '--quiet', '--detach', input.baseCommit);
    const proofPath = path.join(root, input.proofPath);
    let directory = root;
    for (const component of input.proofPath.split('/').slice(0, -1)) {
      directory = path.join(directory, component);
      if (!fs.existsSync(directory)) fs.mkdirSync(directory);
      if (fs.lstatSync(directory).isSymbolicLink() || !fs.lstatSync(directory).isDirectory())
        throw new Error('Refutation proof parent is not a regular directory');
    }
    fs.writeFileSync(proofPath, source, { flag: 'wx' });
    git(root, 'add', '--', input.proofPath);
    git(
      root,
      '-c',
      'user.name=DeepScientist verifier',
      '-c',
      'user.email=verifier@example.invalid',
      '-c',
      'commit.gpgsign=false',
      'commit',
      '--quiet',
      '-m',
      'Isolated route refutation proof'
    );
    return {
      root,
      sourceHash: digest(source),
      commit: git(root, 'rev-parse', 'HEAD').trim(),
      dispose: () => fs.rmSync(root, { recursive: true, force: true }),
    };
  } catch (error) {
    fs.rmSync(root, { recursive: true, force: true });
    throw error;
  }
}

export async function verifyMathRouteRefutation(
  input: MathRouteRefutationBinding & {
    planNodeId: string;
    projectRoot: string;
    proofPath: string;
    theoremName: string;
    targetCommit: string;
  },
  options: Pick<MathematicsVerifierExecutionOptions, 'env' | 'signal' | 'forbiddenImportModules'> = {}
) {
  const target = prepareMathRouteRefutationTarget(input);
  const secret = readMathematicsReceiptSecret();
  const runIdentity = readMathRunHistoryIdentity(options.env ?? process.env);
  if (!secret || !runIdentity) throw new Error('Route refutation requires a bound runtime signing identity');
  const isolated = isolateProof(input);
  let result: Awaited<ReturnType<typeof runFormalVerification>>;
  try {
    result = await runFormalVerification(
      {
        projectRoot: isolated.root,
        proofPath: input.proofPath,
        theoremName: input.theoremName,
        targetCommit: isolated.commit,
        statementHash: target.statementHash,
      },
      { ...options, prepareLocalDependencies: true, expectedDeclarationType: target.expectedDeclarationType }
    );
  } finally {
    isolated.dispose();
  }
  if (
    result.status !== 'kernel_verified' ||
    result.goalsRemaining !== 0 ||
    result.sorryCount !== 0 ||
    result.admitCount !== 0 ||
    !result.theoremDeclarationHash ||
    !result.sourceDeclarationHash ||
    result.axioms.some((axiom) => !isMathFoundationalLeanAxiom(axiom)) ||
    result.targetCommit !== isolated.commit ||
    result.proofHash !== isolated.sourceHash ||
    result.statementHash !== target.statementHash ||
    result.theoremName !== input.theoremName
  ) {
    return Object.freeze({
      status: result.status === 'kernel_verified' ? ('failed' as const) : result.status,
      target,
      verifierResult: result,
    });
  }
  const { expectedDeclarationType: _expectedDeclarationType, ...binding } = target;
  const payload = receiptSchema.parse({
    schema: 'deepscientist.math.route-refutation.v1',
    ...binding,
    runIdentity,
    proofHash: result.proofHash,
    theoremDeclarationHash: result.theoremDeclarationHash,
    targetCommit: input.targetCommit,
    verificationCommit: result.targetCommit,
    proofPath: result.proofPath,
    theoremName: result.theoremName,
  });
  const encoded = Buffer.from(canonicalMathJson(payload)).toString('base64url');
  const signature = crypto
    .createHmac('sha256', secret)
    .update(prefix + encoded)
    .digest('hex');
  return Object.freeze({
    status: 'kernel_verified' as const,
    target,
    verifierResult: result,
    reference: `${prefix}${encoded}.${signature}`,
    receipt: payload,
  });
}

export function readTrustedMathRouteRefutation(
  reference: string,
  binding: MathRouteRefutationBinding,
  secret = readMathematicsReceiptSecret(),
  runIdentity = readMathRunHistoryIdentity()
) {
  if (!secret || !runIdentity || !reference.startsWith(prefix) || reference.length > 32_000) return undefined;
  try {
    const [encoded, signature, extra] = reference.slice(prefix.length).split('.');
    if (extra || !/^[a-f0-9]{64}$/u.test(signature ?? '')) return undefined;
    const expected = crypto
      .createHmac('sha256', secret)
      .update(prefix + encoded)
      .digest();
    if (!crypto.timingSafeEqual(expected, Buffer.from(signature, 'hex'))) return undefined;
    const receipt = receiptSchema.parse(JSON.parse(Buffer.from(encoded, 'base64url').toString('utf8')));
    if (receipt.runIdentity !== runIdentity) return undefined;
    const target = prepareMathRouteRefutationTarget({ ...binding, planNodeId: receipt.planNodeId });
    const { expectedDeclarationType: _expectedDeclarationType, ...identity } = target;
    if (Object.entries(identity).some(([key, value]) => receipt[key as keyof typeof receipt] !== value))
      return undefined;
    return Object.freeze(receipt);
  } catch {
    return undefined;
  }
}
