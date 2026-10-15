import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from './contracts';
import { canonicalMathJson, mathDigest, readMathJson, writeMathJsonDurable } from './mathRuntimeIo';
import { hashMathFormalSourceDeclaration } from './leanSource';
import { mathGitText } from './mathGit';
import { assertMathCanonicalPath } from './paths';

export const LOCAL_EXAMPLE_TOOLCHAIN = 'leanprover/lean4:v4.33.0';
export const LOCAL_EXAMPLE_STATEMENT = 'namespace Tutorial\n\ntheorem add_zero (n : Nat) : n + 0 = n := by sorry\n\ntheorem zero_add (n : Nat) : 0 + n = n := by sorry\n\nend Tutorial\n';
export const LOCAL_EXAMPLE_PROOF = LOCAL_EXAMPLE_STATEMENT.replace('by sorry', 'by rfl').replace('by sorry', 'by exact Nat.zero_add n');
export const LOCAL_EXAMPLE_FAILED_PROOF = LOCAL_EXAMPLE_STATEMENT.replaceAll('by sorry', 'by rfl');
const trustedSources = {
  'Challenge.lean': LOCAL_EXAMPLE_STATEMENT,
  'lean-toolchain': `${LOCAL_EXAMPLE_TOOLCHAIN}\n`,
  'lakefile.toml': 'name = "theorem_os_tutorial"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Submission"\n',
  'lake-manifest.json': JSON.stringify({ version: '1.1.0', packagesDir: '.lake/packages', packages: [], name: 'theorem_os_tutorial', lakeDir: '.lake' }) + '\n',
};
const contract = (): MathProblemContract => {
  const informalStatement = 'Prove that adding zero on either side leaves every natural number unchanged.';
  const payloads = canonicalMathProblemStatementPayloads({ informalStatement, formalStatement: LOCAL_EXAMPLE_STATEMENT, assumptions: [] });
  return { problemId: 'tutorial-addition', informalStatement, formalStatement: LOCAL_EXAMPLE_STATEMENT,
    assumptions: [], knownTraps: [], acceptanceCriteria: ['Both original targets pass independent Lean kernel verification.'],
    officialVerificationCommand: 'Local tutorial: host Lean verification, not an official benchmark.',
    statementHash: mathDigest(payloads.informal), leanStatementHash: mathDigest(payloads.lean) };
};
const obligations = () => ['Tutorial.add_zero', 'Tutorial.zero_add'].map(name => ({
  name, declarationHash: hashMathFormalSourceDeclaration(LOCAL_EXAMPLE_STATEMENT, name)!,
}));
const receiptSchema = z.object({
  schema: z.literal('theorem-os.local-example.v1'), workspaceRoot: z.string(), projectRoot: z.string(),
  activeProblemPath: z.string(), contract: z.record(z.unknown()),
  trustedFiles: z.array(z.string()), solverOwnedFiles: z.array(z.string()),
  publicObligations: z.array(z.object({ name: z.string(), declarationHash: z.string() }).strict()),
}).strict();
export type LocalExampleReceipt = {
  schema: 'theorem-os.local-example.v1'; workspaceRoot: string; projectRoot: string; activeProblemPath: string;
  contract: MathProblemContract; trustedFiles: string[]; solverOwnedFiles: string[];
  publicObligations: { name: string; declarationHash: string }[];
};

export function bootstrapLocalExample(workspace: string): LocalExampleReceipt {
  workspace = path.resolve(workspace);
  assertMathCanonicalPath(workspace);
  if (fs.existsSync(workspace)) throw new Error('Example workspace already exists; use a new directory.');
  const projectRoot = path.join(workspace, 'generated/addition');
  fs.mkdirSync(projectRoot, { recursive: true, mode: 0o700 });
  for (const [file, source] of Object.entries({ ...trustedSources, 'Submission.lean': LOCAL_EXAMPLE_STATEMENT }))
    fs.writeFileSync(path.join(projectRoot, file), source, { flag: 'wx', mode: 0o600 });
  const receipt: LocalExampleReceipt = { schema: 'theorem-os.local-example.v1', workspaceRoot: workspace,
    projectRoot, activeProblemPath: path.join(workspace, 'active-problem.json'), contract: contract(),
    trustedFiles: Object.keys(trustedSources), solverOwnedFiles: ['Submission.lean'], publicObligations: obligations() };
  const git = (args: string[]) => mathGitText(workspace, args, { timeout: 30_000, maxBuffer: 8_000 });
  git(['init', '--quiet']);
  git(['add', '--', 'generated']);
  git(['-c', 'user.name=TheoremOS', '-c', 'user.email=theoremos@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Prepare the addition tutorial']);
  fs.appendFileSync(path.join(workspace, '.git/info/exclude'), '\n/active-problem.json\n**/.lake/\n');
  writeMathJsonDurable(receipt.activeProblemPath, receipt);
  return receipt;
}

/** A tutorial receipt cannot redefine the bundled problem, targets or protected inputs. */
export function readLocalExampleReceipt(file: string): LocalExampleReceipt {
  const parsed = receiptSchema.parse(readMathJson(file));
  const workspace = fs.realpathSync(parsed.workspaceRoot);
  assertMathCanonicalPath(workspace);
  const project = path.join(workspace, 'generated/addition');
  if (parsed.workspaceRoot !== workspace || parsed.projectRoot !== project ||
      parsed.activeProblemPath !== path.join(workspace, 'active-problem.json') || path.resolve(file) !== parsed.activeProblemPath ||
      canonicalMathJson(parsed.contract) !== canonicalMathJson(contract()) ||
      canonicalMathJson(parsed.publicObligations) !== canonicalMathJson(obligations()) ||
      canonicalMathJson(parsed.trustedFiles) !== canonicalMathJson(Object.keys(trustedSources)) ||
      canonicalMathJson(parsed.solverOwnedFiles) !== canonicalMathJson(['Submission.lean']))
    throw new Error('Local example identity changed; prepare a new case.');
  for (const [relative, source] of Object.entries(trustedSources)) {
    const target = path.join(project, relative);
    assertMathCanonicalPath(target);
    if (fs.readFileSync(target, 'utf8') !== source) throw new Error(`Local example protected file changed: ${relative}`);
  }
  return parsed as unknown as LocalExampleReceipt;
}
