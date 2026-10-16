import { parse as parseToml } from 'smol-toml';
import { z } from 'zod';
import mathlibResource from '../../resources/mathlib/environment.json';
import { canonicalMathJson, mathDigest } from './mathRuntimeIo';
import { LOCAL_EXAMPLE_TOOLCHAIN } from './localExample';

export type LeanTaskEnvironment = 'standard' | 'mathlib';
export type LeanTaskEnvironmentConfig = Readonly<{
  id: LeanTaskEnvironment;
  toolchain: string;
  files: Readonly<Record<string, string>>;
  dependencyDigest: string;
  mathlibRevision?: string;
}>;

const standardFiles = Object.freeze({
  'lean-toolchain': `${LOCAL_EXAMPLE_TOOLCHAIN}\n`,
  'lakefile.toml': 'name = "theorem_os_problem"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "Submission"\n',
  'lake-manifest.json': JSON.stringify({ version: '1.1.0', packagesDir: '.lake/packages', packages: [],
    name: 'theorem_os_problem', lakeDir: '.lake' }) + '\n',
});

function configuration(id: LeanTaskEnvironment, toolchain: string, files: Readonly<Record<string, string>>,
  mathlibRevision?: string): LeanTaskEnvironmentConfig {
  return Object.freeze({ id, toolchain, files,
    ...(mathlibRevision ? { mathlibRevision } : {}),
    dependencyDigest: mathDigest(canonicalMathJson({ schema: 'theorem-os.lean-task-environment.v1', id, toolchain, files,
      ...(mathlibRevision ? { mathlibRevision } : {}) })) });
}

const standard = configuration('standard', LOCAL_EXAMPLE_TOOLCHAIN, standardFiles);
const gitRevision = z.string().regex(/^[0-9a-f]{40}$/u);
const resource = z.object({
  schema: z.literal('theorem-os.lean-task-mathlib.v1'), id: z.literal('mathlib'),
  toolchain: z.literal(LOCAL_EXAMPLE_TOOLCHAIN), mathlibRevision: gitRevision,
  lakefile: z.string().min(1), manifest: z.object({
    version: z.literal('1.2.0'), packagesDir: z.literal('.lake/packages'),
    packages: z.array(z.object({
      url: z.string().url().startsWith('https://github.com/'), type: z.literal('git'), subDir: z.null(),
      scope: z.string().min(1), rev: gitRevision, name: z.string().regex(/^[A-Za-z_][A-Za-z0-9_]*$/u),
      manifestFile: z.literal('lake-manifest.json'), inputRev: z.string().min(1), inherited: z.boolean(),
      configFile: z.enum(['lakefile.toml', 'lakefile.lean']),
    }).strict()).min(1), name: z.literal('theorem_os_problem'), lakeDir: z.literal('.lake'), fixedToolchain: z.literal(true),
  }).strict(),
}).strict().parse(mathlibResource);
const rootPackage = resource.manifest.packages.find(item => item.name === 'mathlib');
const lakefile = parseToml(resource.lakefile);
const requirements = lakefile.require as { name?: unknown; git?: unknown; rev?: unknown }[] | undefined;
if (!rootPackage || rootPackage.rev !== resource.mathlibRevision || rootPackage.inputRev !== resource.mathlibRevision ||
    rootPackage.url !== 'https://github.com/leanprover-community/mathlib4.git' || rootPackage.inherited ||
    rootPackage.configFile !== 'lakefile.lean' || requirements?.length !== 1 || requirements[0]?.name !== 'mathlib' ||
    requirements[0]?.git !== rootPackage.url || requirements[0]?.rev !== resource.mathlibRevision ||
    new Set(resource.manifest.packages.map(item => item.name)).size !== resource.manifest.packages.length ||
    resource.manifest.packages.some(item => item.name !== 'mathlib' && !item.inherited))
  throw new Error('lean_task_mathlib_resource_invalid');
const mathlib = configuration('mathlib', resource.toolchain, Object.freeze({
  'lean-toolchain': `${resource.toolchain}\n`,
  'lakefile.toml': resource.lakefile,
  'lake-manifest.json': JSON.stringify(resource.manifest, null, 2) + '\n',
}), resource.mathlibRevision);

/** Dependency choices are supplied by this runtime, never by task source or a caller URL. */
export function getLeanTaskEnvironment(id: LeanTaskEnvironment = 'standard'): LeanTaskEnvironmentConfig {
  if (id === 'standard') return standard;
  if (id === 'mathlib') return mathlib;
  throw new Error('lean_task_environment_unavailable');
}
