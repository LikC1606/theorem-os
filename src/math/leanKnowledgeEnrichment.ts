import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { bindLeanPackages, prepareLeanDiagnosticOverrides, runLeanDiagnostics } from './leanDiagnostics';
import { leanDiagnosticEnvironmentIdentity } from './leanResidualGoals';
import { leanReferenceCommands, parseLeanReferenceReport, parseLeanReferences, type LeanDeclarationReferences } from './leanReferences';
import { leanStatementContextCommands, parseLeanStatementContexts, type LeanStatementContext } from './leanStatementContext';
import { checkResolvedLeanToolchainReadiness } from './leanToolchainReadiness';
import { resolveMathProofEnvironment } from './mathProofEnvironment';
import { resolveMathematicsRuntimeEnvironment } from './mathRuntimeEnvironment';
import { canonicalMathJson, mathDigest, readMathFile, writeMathJsonDurable } from './mathRuntimeIo';
import { inspectLeanDeclarationRegions, inspectScopedLeanDeclarations } from './leanSource';
import { assertMathCanonicalPath } from './paths';
import { resolveMathematicsLakePackagesCache } from './verifier';

export type LeanKnowledgeEnrichmentRoot = Readonly<{ id: string; name: string; file: string }>;
export type LeanKnowledgeEnrichmentSource = Readonly<{ file: string; digest: string; bytes: number }>;
export type LeanKnowledgeEnrichmentConfiguration = Readonly<{ file: string; digest: string | null; bytes: number }>;
export type LeanKnowledgeEnrichmentArtifact = Readonly<{
  kind: 'query' | 'full-type' | 'statement-context' | 'diagnostics'; path: string; digest: string; bytes: number;
}>;
export type LeanKnowledgeEnrichmentIdentity = {
  sourceDigest: string; sources: LeanKnowledgeEnrichmentSource[]; configuration: LeanKnowledgeEnrichmentConfiguration[];
  executionConfiguration?: LeanKnowledgeEnrichmentConfiguration[]; executionSourceDigest?: string;
  toolchain: string | null; toolIdentity?: string;
  tools: { command: 'lean' | 'lake'; file: string; digest: string }[];
  environmentDigest?: string; sealedEnvironmentIdentity?: string;
  collector: { version: string; source: string; digest: string };
};
export type LeanKnowledgeRootEnrichment = LeanKnowledgeEnrichmentRoot & {
  status: 'collected' | 'failed' | 'unavailable'; sourceDigest?: string; declarationDigest?: string;
  fullType?: string; universes?: string[]; statementContext?: LeanStatementContext; references?: LeanDeclarationReferences;
  omissions: string[]; queryDigest?: string; artifacts: LeanKnowledgeEnrichmentArtifact[]; reason?: string;
};
export type LeanKnowledgeEnrichment = {
  schema: 'theorem-os.lean-knowledge-enrichment.v1'; authority: 'advisory-lean-process'; proofAcceptance: 'not-assessed';
  identity: LeanKnowledgeEnrichmentIdentity; roots: LeanKnowledgeRootEnrichment[];
};

const configurationFiles = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
const maxFileBytes = 16 * 1024 * 1024, maxTotalBytes = 256 * 1024 * 1024;
export type LeanKnowledgeCollectorVersion = 'complete-proof-knowledge-collector-v1' | 'complete-proof-knowledge-collector-v2' |
  'complete-proof-knowledge-collector-v3';
const currentCollectorVersion: LeanKnowledgeCollectorVersion = 'complete-proof-knowledge-collector-v3';
const enrichmentReferenceLimits = { maxBytes: 256000, maxReferences: 4096, fuel: 2000000 } as const;
const typeExportBound = (version: LeanKnowledgeCollectorVersion) => version === 'complete-proof-knowledge-collector-v1'
  ? 24000 : version === 'complete-proof-knowledge-collector-v2' ? 256000 : 2_000_000;
function collectorVersion(version: LeanKnowledgeCollectorVersion) {
  if (version !== 'complete-proof-knowledge-collector-v1' && version !== 'complete-proof-knowledge-collector-v2' &&
      version !== 'complete-proof-knowledge-collector-v3')
    throw new Error('math_knowledge_enrichment_collector_changed');
  return version;
}
const sortFiles = <T extends { file: string }>(files: T[]) => files.sort((a, b) => a.file < b.file ? -1 : a.file > b.file ? 1 : 0);
export const leanKnowledgeSourceDigest = (sources: readonly LeanKnowledgeEnrichmentSource[],
  configuration: readonly LeanKnowledgeEnrichmentConfiguration[]) => mathDigest(canonicalMathJson({ sources, configuration }));

function fullTypeCommands(name: string, output: string, version: LeanKnowledgeCollectorVersion) {
  return ['set_option pp.all true', 'set_option pp.fullNames true', 'set_option pp.notation false',
    'set_option pp.proofs true', 'set_option pp.universes true', 'set_option pp.explicit true',
    'set_option pp.deepTerms true', 'set_option pp.maxSteps 2000000',
    'run_cmd Lean.Elab.Command.liftTermElabM do',
    `  let root <- Lean.getConstInfo (${JSON.stringify(name)}.toName)`,
    '  unless root.type.hasMVar == false && root.type.hasLevelMVar == false && root.type.hasFVar == false && root.type.hasLooseBVars == false do',
    '    throwError "Knowledge root type is not closed"',
    version === 'complete-proof-knowledge-collector-v1' ? '  let fullType := (<- Lean.Meta.ppExpr root.type).pretty'
      : '  let fullType := (<- Lean.Meta.ppExpr root.type).pretty (width := 256000)',
    `  if fullType.utf8ByteSize > ${typeExportBound(version)} then throwError "Knowledge root type exceeds export bound"`,
    '  if fullType.contains \'\u22ef\' then throwError "Knowledge root type contains an omitted term"',
    '  Lean.Elab.Term.withLevelNames root.levelParams do',
    '    let parsed <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "term") fullType with',
    '      | .ok stx => pure stx', '      | .error message => throwError "{message}"',
    '    let expression <- Lean.Elab.Term.elabType parsed',
    '    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing',
    '    let expression <- Lean.instantiateMVars expression',
    '    if expression.hasMVar || expression.hasLevelMVar || expression.hasFVar || expression.hasLooseBVars then throwError "Knowledge type export is incomplete"',
    '    unless (<- Lean.Meta.isDefEq expression root.type) do throwError "Knowledge type export changed its meaning"',
    `  let report := Lean.Json.mkObj [("name", Lean.toJson ${JSON.stringify(name)}), ("fullType", Lean.toJson fullType),`,
    '    ("universes", Lean.toJson (root.levelParams.map Lean.Name.toString)), ("typeComplete", Lean.toJson true)]',
    `  Lean.Core.liftIOCore <| IO.FS.writeFile ${JSON.stringify(output)} report.compress`].join('\n');
}

function contextCommands(root: { id: string; name: string }, modules: readonly { module: string; file: string }[],
  output: string, version: LeanKnowledgeCollectorVersion) {
  // Full proof-aware export is independent of the bounded, readable statement context.
  const reset = version === 'complete-proof-knowledge-collector-v1' ? [] : [
    'set_option pp.all false', 'set_option pp.explicit false', 'set_option pp.universes false', 'set_option pp.deepTerms false',
  ];
  return [...reset, leanStatementContextCommands([root], modules, output,
    version === 'complete-proof-knowledge-collector-v1' ? undefined : { omitOversizedType: true })].join('\n');
}

/** Bind the actual generator text, including the two shared collectors and full proof-aware type export. */
export function leanKnowledgeCollectorIdentity(version: LeanKnowledgeCollectorVersion = currentCollectorVersion) {
  collectorVersion(version);
  const source = canonicalMathJson({ fullType: fullTypeCommands('__ROOT__', '__FULL_TYPE__', version),
    references: leanReferenceCommands('__ROOT__', [{ module: '__MODULE__', file: '__FILE__' }], '__REFERENCES__',
      version === 'complete-proof-knowledge-collector-v1' ? undefined : enrichmentReferenceLimits),
    context: contextCommands({ id: '__ID__', name: '__ROOT__' }, [{ module: '__MODULE__', file: '__FILE__' }], '__CONTEXT__', version) });
  return { version, source, digest: mathDigest(source) };
}

export function leanKnowledgeQuery(root: LeanKnowledgeEnrichmentRoot,
  modules: readonly { module: string; file: string }[], index: number,
  version: LeanKnowledgeCollectorVersion = currentCollectorVersion) {
  collectorVersion(version);
  const module = modules.find(item => item.file === root.file);
  if (!module || !Number.isSafeInteger(index) || index < 0 || !modules.every(item =>
    /^(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\r\n]+»)(?:\.(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\r\n]+»))*$/u.test(item.module)))
    throw new Error('math_knowledge_enrichment_module_invalid');
  const prefix = `KnowledgeEnrichment${index}`, contextOutput = `.lake/${prefix}-context.json`,
    typeOutput = `.lake/${prefix}-type.json`, referenceMarker = `KNOWLEDGE_REFERENCES_${index}:`;
  const source = ['import Lean', `import ${module.module}`, fullTypeCommands(root.name, typeOutput, version),
    ...leanReferenceCommands(root.name, modules, referenceMarker,
      version === 'complete-proof-knowledge-collector-v1' ? undefined : enrichmentReferenceLimits),
    contextCommands({ id: root.id, name: root.name }, modules, contextOutput, version)].join('\n') + '\n';
  return { source, queryFile: `${prefix}.lean`, referenceMarker, contextOutput, typeOutput };
}

/** Lean versions use both JSON `data` messages and rendered info lines. */
function referenceOutput(stdout: string) {
  return stdout.split('\n').map(line => {
    try {
      const message: unknown = JSON.parse(line);
      if (message && typeof message === 'object') {
        const value = message as { data?: unknown; message?: unknown };
        if (typeof value.data === 'string') return value.data;
        if (typeof value.message === 'string') return value.message;
      }
    } catch { /* Legacy rendered Lean output. */ }
    return line;
  }).join('\n');
}

export function parseLeanKnowledgeContext(text: string, id: string,
  version: LeanKnowledgeCollectorVersion = currentCollectorVersion): { context?: LeanStatementContext; omissions: string[] } {
  collectorVersion(version);
  if (version !== 'complete-proof-knowledge-collector-v1') {
    if (Buffer.byteLength(text) > 4_000_000) throw new Error('math_statement_elaboration_invalid');
    const reports = JSON.parse(text);
    const context = Array.isArray(reports) && reports.length === 1 && reports[0]?.id === id ? reports[0].context : undefined;
    if (context && typeof context === 'object' && 'unavailable' in context) {
      if (Object.keys(reports[0]).sort().join(',') !== 'context,id' ||
          Object.keys(context).sort().join(',') !== 'bytes,limit,unavailable' ||
          context.unavailable !== 'statement-type-export-bound' || context.limit !== 24000 ||
          !Number.isSafeInteger(context.bytes) || context.bytes <= context.limit)
        throw new Error('math_statement_elaboration_invalid');
      return { omissions: ['statement-context:statement-type-export-bound'] };
    }
  }
  const context = parseLeanStatementContexts(text, [id]).get(id)!;
  return { context, omissions: [...context.omitted] };
}

type ReferenceIdentity = { name: string; modules: readonly { module: string; file: string }[] };
const referenceOptions = (expected?: ReferenceIdentity) => ({ ...enrichmentReferenceLimits,
  ...(expected ? { expectedTheoremName: expected.name, expectedModules: expected.modules } : {}) });

export function parseLeanKnowledgeReferences(stdout: string, marker: string, files: readonly string[],
  version: LeanKnowledgeCollectorVersion = currentCollectorVersion, expected?: ReferenceIdentity) {
  collectorVersion(version);
  const output = referenceOutput(stdout);
  if (version === 'complete-proof-knowledge-collector-v1') return parseLeanReferences(output, marker, files);
  const report = parseLeanReferenceReport(output, marker, files, referenceOptions(expected));
  return report.status === 'complete' ? report.references : undefined;
}

export function leanKnowledgeReferenceOmissions(stdout: string, marker: string, files: readonly string[],
  version: LeanKnowledgeCollectorVersion = currentCollectorVersion, expected?: ReferenceIdentity): string[] {
  collectorVersion(version);
  if (version === 'complete-proof-knowledge-collector-v1')
    return parseLeanReferences(referenceOutput(stdout), marker, files) ? [] : ['proof-and-statement-references-unavailable'];
  const report = parseLeanReferenceReport(referenceOutput(stdout), marker, files, referenceOptions(expected));
  return report.status === 'complete' ? [] : ['proof-and-statement-references-unavailable', `proof-and-statement-references:${report.reason}`];
}

function readSource(file: string) {
  assertMathCanonicalPath(file);
  const loaded = readMathFile(file, maxFileBytes);
  return { ...loaded, text: new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(loaded.bytes) };
}

function snapshot(project: string) {
  const files = new Map<string, ReturnType<typeof readSource>>();
  const directories = [''];
  let bytes = 0;
  const add = (file: string) => {
    const source = readSource(path.join(project, file)); bytes += source.bytes.length;
    if (files.size >= 4096 || bytes > maxTotalBytes) throw new Error('math_knowledge_enrichment_sources_too_large');
    files.set(file, source);
    return source;
  };
  for (let index = 0; index < directories.length; index++) {
    const relative = directories[index];
    for (const entry of fs.readdirSync(path.join(project, relative), { withFileTypes: true })) {
      if (entry.name.startsWith('.')) continue;
      const file = relative ? `${relative}/${entry.name}` : entry.name;
      if (entry.isSymbolicLink()) throw new Error('math_knowledge_enrichment_source_linked');
      if (entry.isDirectory()) {
        if (directories.length >= 4096) throw new Error('math_knowledge_enrichment_sources_too_large');
        directories.push(file);
      }
      else if (entry.isFile() && entry.name.endsWith('.lean') && file !== 'lakefile.lean' && entry.name !== 'Solution.lean')
        add(file);
    }
  }
  const sources = sortFiles([...files].map(([file, source]) => ({ file, digest: mathDigest(source.bytes), bytes: source.bytes.length })));
  const configuration = configurationFiles.map(file => {
    const absolute = path.join(project, file); assertMathCanonicalPath(absolute);
    if (!fs.lstatSync(absolute, { throwIfNoEntry: false })) return { file, digest: null, bytes: 0 };
    const source = add(file);
    return { file, digest: mathDigest(source.bytes), bytes: source.bytes.length };
  });
  if (files.size > 4096 || [...files.values()].reduce((sum, source) => sum + source.bytes.length, 0) > maxTotalBytes)
    throw new Error('math_knowledge_enrichment_sources_too_large');
  return { files, sources, configuration, sourceDigest: leanKnowledgeSourceDigest(sources, configuration) };
}

/** Resolve an already installed pin without invoking an elan shim that might download it. */
function installedTools(project: string, toolchain: string | null, env: NodeJS.ProcessEnv) {
  if (!toolchain || !/^(?:leanprover\/lean4:)?v?\d+\.\d+\.\d+(?:-rc\d+)?$/u.test(toolchain)) return;
  const candidates: string[] = [];
  for (const directory of (env.PATH ?? '').split(path.delimiter).filter(Boolean)) {
    if (!path.isAbsolute(directory)) continue;
    for (const command of ['lean', 'lake']) {
      const file = path.join(directory, command);
      try {
        const real = fs.realpathSync(file), bin = path.dirname(real), prefix = path.dirname(bin);
        if (path.basename(real) === command && fs.existsSync(path.join(prefix, 'lib', 'lean')) &&
            fs.existsSync(path.join(bin, 'lean')) && fs.existsSync(path.join(bin, 'lake'))) candidates.push(bin);
      } catch { /* Try only installed absolute tool paths. */ }
    }
  }
  const pin = toolchain.startsWith('leanprover/') ? toolchain : `leanprover/lean4:${toolchain.startsWith('v') ? toolchain : `v${toolchain}`}`;
  const elanRoot = env.ELAN_HOME || path.join(os.homedir(), '.elan');
  const pinned = path.join(elanRoot, 'toolchains', pin.replaceAll('/', '--').replaceAll(':', '---'), 'bin');
  if (fs.existsSync(path.join(pinned, 'lean')) && fs.existsSync(path.join(pinned, 'lake'))) candidates.unshift(pinned);
  for (const bin of [...new Set(candidates)]) {
    const runtime = resolveMathematicsRuntimeEnvironment({ ...env, ELAN_HOME: path.dirname(bin),
      DEEPSCIENTIST_MATH_ENV_FILE: path.join(project, '.lake', 'nonexistent-knowledge-environment.env'),
      PATH: [bin, ...(env.PATH ?? '').split(path.delimiter).filter(directory => directory && path.isAbsolute(directory) && directory !== bin)].join(path.delimiter) });
    const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env: runtime });
    if (readiness.status === 'ready' && readiness.leanPath && readiness.lakePath) {
      const tools = (['lean', 'lake'] as const).map(command => {
        const file = fs.realpathSync(command === 'lean' ? readiness.leanPath! : readiness.lakePath!);
        return { command, file, digest: mathDigest(fs.readFileSync(file)) };
      });
      return { env: runtime, tools };
    }
  }
}

/** Explicit offline collection from complete proofs; it never creates solver or acceptance receipts. */
export async function collectLeanKnowledgeEnrichment(input: {
  projectRoot: string; roots: readonly LeanKnowledgeEnrichmentRoot[]; env?: NodeJS.ProcessEnv;
  queryIndices?: readonly number[];
  signal?: AbortSignal; timeoutMs?: number;
}): Promise<LeanKnowledgeEnrichment> {
  const timeoutMs = input.timeoutMs ?? Infinity;
  if (!(timeoutMs === Infinity || Number.isSafeInteger(timeoutMs) && timeoutMs >= 0) || !input.roots.length || input.roots.length > 4096 ||
      input.queryIndices !== undefined && (input.queryIndices.length !== input.roots.length ||
        new Set(input.queryIndices).size !== input.queryIndices.length || input.queryIndices.some(index => !Number.isSafeInteger(index) || index < 0 || index >= 4096)) ||
      new Set(input.roots.map(root => root.id)).size !== input.roots.length || input.roots.some(root =>
        !root.id || root.id.length > 256 || !root.name || root.name.length > 1000 || !root.file || root.file.length > 4096))
    throw new Error('math_knowledge_enrichment_input_invalid');
  const project = fs.realpathSync(input.projectRoot); assertMathCanonicalPath(project);
  const initial = snapshot(project), runtime = resolveMathematicsRuntimeEnvironment(input.env ?? process.env);
  const toolchain = initial.files.get('lean-toolchain')?.text.trim() || null;
  const identity: LeanKnowledgeEnrichmentIdentity = { sourceDigest: initial.sourceDigest, sources: initial.sources,
    configuration: initial.configuration, toolchain, tools: [], collector: leanKnowledgeCollectorIdentity() };
  const result: LeanKnowledgeEnrichment = { schema: 'theorem-os.lean-knowledge-enrichment.v1', authority: 'advisory-lean-process',
    proofAcceptance: 'not-assessed', identity, roots: [] };
  for (const root of input.roots) {
    const source = initial.files.get(root.file), regions = source && inspectLeanDeclarationRegions(source.text);
    const declarations = source && inspectScopedLeanDeclarations(source.text).filter(item => item.qualifiedName === root.name);
    const region = declarations?.length === 1 ? regions?.find(item => item.startOffset === declarations[0].startOffset) : undefined;
    result.roots.push({ ...root, status: region ? 'unavailable' : 'failed',
      ...(source ? { sourceDigest: mathDigest(source.bytes) } : {}),
      ...(region ? { declarationDigest: mathDigest(source!.text.slice(region.startOffset, region.endOffset)) } : {}),
      omissions: [], artifacts: [], reason: region ? 'pinned-toolchain-unavailable' : 'root-declaration-missing-or-ambiguous' });
  }
  const tools = installedTools(project, toolchain, runtime);
  if (!tools) return result;
  identity.tools = tools.tools;
  const temporary = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-knowledge-enrichment-')));
  const clone = path.join(temporary, 'project'); fs.mkdirSync(clone, { mode: 0o700 });
  const outputDirectory = path.join(project, '.lake', 'knowledge-enrichment', crypto.randomUUID());
  assertMathCanonicalPath(outputDirectory); fs.mkdirSync(outputDirectory, { recursive: true, mode: 0o700 });
  const started = Date.now();
  const remaining = () => timeoutMs === Infinity ? Infinity : Math.max(0, timeoutMs - (Date.now() - started));
  const retain = (kind: LeanKnowledgeEnrichmentArtifact['kind'], filename: string, text: string): LeanKnowledgeEnrichmentArtifact => {
    const file = path.join(outputDirectory, filename); assertMathCanonicalPath(file);
    fs.writeFileSync(file, text, { flag: 'wx', mode: 0o400 });
    return { kind, path: path.relative(project, file).replaceAll(path.sep, '/'), digest: mathDigest(text), bytes: Buffer.byteLength(text) };
  };
  const currentInputs = () => {
    const current = snapshot(project);
    if (current.sourceDigest !== initial.sourceDigest) throw new Error('math_knowledge_enrichment_sources_changed');
    for (const [file, source] of initial.files) if (current.files.get(file)?.identity !== source.identity)
      throw new Error('math_knowledge_enrichment_sources_changed');
  };
  try {
    for (const [file, source] of initial.files) {
      const target = path.join(clone, file); assertMathCanonicalPath(target);
      fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 }); fs.writeFileSync(target, source.bytes, { mode: 0o600 });
    }
    currentInputs();
    const sealed = resolveMathProofEnvironment(project, tools.env);
    const packages = sealed?.packagesRoot ?? path.join(project, '.lake', 'packages');
    const packageManifest = initial.files.get('lake-manifest.json');
    const declaredPackages = packageManifest ? JSON.parse(packageManifest.text)?.packages : undefined;
    const implicitPackages = !sealed && resolveMathematicsLakePackagesCache(clone, tools.env);
    // General diagnostics can discover global mutable caches; they cannot supply historical environment identity.
    if (!sealed && (implicitPackages || Array.isArray(declaredPackages) && declaredPackages.length > 0 || fs.existsSync(packages) ||
        runtime.LEAN_PATH?.trim() || runtime.LEAN_SYSROOT?.trim())) {
      for (const root of result.roots) if (root.status !== 'failed') root.reason = 'unsealed-dependencies-unavailable';
      return result;
    }
    if (fs.existsSync(packages)) bindLeanPackages(clone, packages);
    prepareLeanDiagnosticOverrides(clone);
    if (sealed) {
      sealed.verify();
      if (resolveMathProofEnvironment(clone, tools.env)?.identity !== sealed.identity) throw new Error('math_knowledge_enrichment_environment_changed');
      identity.sealedEnvironmentIdentity = sealed.identity;
    }
    const actual = leanDiagnosticEnvironmentIdentity(clone, tools.env);
    identity.environmentDigest = actual.environmentDigest; identity.toolIdentity = actual.toolIdentity;
    const execution = snapshot(clone);
    identity.executionConfiguration = execution.configuration;
    identity.executionSourceDigest = execution.sourceDigest;
    if (!identity.toolIdentity) {
      for (const root of result.roots) if (root.status !== 'failed') root.reason = 'actual-tool-identity-unavailable';
      return result;
    }
    for (let index = 0; index < result.roots.length; index++) {
      const root = result.roots[index];
      if (root.status === 'failed') continue;
      if (input.signal?.aborted || remaining() <= 0) { root.reason = input.signal?.aborted ? 'collection-aborted' : 'collection-budget-exhausted'; continue; }
      let queryFile: string | undefined;
      try {
        assertMathConstructionSources(clone, [root.file]);
        const modules = mathLocalModuleBuildOrder(clone, root.file);
        const { source: commands, queryFile: filename, contextOutput, typeOutput, referenceMarker } =
          leanKnowledgeQuery(root, modules, input.queryIndices?.[index] ?? index);
        if (initial.files.has(filename)) { root.reason = 'query-source-name-collision'; continue; }
        queryFile = filename;
        fs.writeFileSync(path.join(clone, queryFile), commands, { mode: 0o600 });
        root.artifacts.push(retain('query', `${index}-query.lean`, commands)); root.queryDigest = mathDigest(commands);
        const diagnostics = await runLeanDiagnostics({ projectRoot: clone, files: [queryFile], env: tools.env,
          signal: input.signal, timeoutMs: remaining(), outputLimit: 4_000_000 });
        root.artifacts.push(retain('diagnostics', `${index}-diagnostics.json`, canonicalMathJson(diagnostics)));
        currentInputs();
        for (const [file, source] of initial.files) {
          const current = readSource(path.join(clone, file));
          if (file !== '.lake/package-overrides.json' && mathDigest(current.bytes) !== mathDigest(source.bytes))
            throw new Error('math_knowledge_enrichment_projection_changed');
        }
        const aborted = 'aborted' in diagnostics && diagnostics.aborted === true;
        if (diagnostics.exitCode !== 0 || diagnostics.timedOut || aborted) {
          root.status = diagnostics.timedOut || aborted ? 'unavailable' : 'failed';
          root.reason = diagnostics.timedOut ? 'collection-budget-exhausted' : aborted ? 'collection-aborted' : 'lean-collection-failed';
          continue;
        }
        const fullTypeText = readSource(path.join(clone, typeOutput)).text, fullType = JSON.parse(fullTypeText);
        if (!fullType || fullType.name !== root.name || typeof fullType.fullType !== 'string' || !fullType.fullType.trim() ||
            Buffer.byteLength(fullType.fullType) > typeExportBound(currentCollectorVersion) || fullType.typeComplete !== true || !Array.isArray(fullType.universes) ||
            fullType.universes.length > 256 || fullType.universes.some((name: unknown) => typeof name !== 'string' || !name || name.length > 1000))
          throw new Error('math_knowledge_enrichment_type_export_invalid');
        const contextText = readSource(path.join(clone, contextOutput)).text;
        const { context: statementContext, omissions: contextOmissions } = parseLeanKnowledgeContext(contextText, root.id);
        const references = parseLeanKnowledgeReferences(diagnostics.stdout ?? '', referenceMarker, modules.map(item => item.file),
          currentCollectorVersion, { name: root.name, modules });
        root.artifacts.push(retain('full-type', `${index}-type.json`, fullTypeText),
          retain('statement-context', `${index}-context.json`, contextText));
        root.status = 'collected'; root.reason = undefined; root.fullType = fullType.fullType; root.universes = fullType.universes;
        root.statementContext = statementContext;
        if (references) root.references = references;
        root.omissions = [...contextOmissions, ...leanKnowledgeReferenceOmissions(diagnostics.stdout ?? '', referenceMarker,
          modules.map(item => item.file), currentCollectorVersion, { name: root.name, modules })];
      } catch (error) {
        root.status = input.signal?.aborted ? 'unavailable' : 'failed';
        root.reason = input.signal?.aborted ? 'collection-aborted' : error instanceof Error ? error.message : 'lean-collection-failed';
      } finally { if (queryFile) fs.rmSync(path.join(clone, queryFile), { force: true }); }
    }
    currentInputs();
    if (sealed) sealed.verify();
    if (leanDiagnosticEnvironmentIdentity(clone, tools.env).toolIdentity !== identity.toolIdentity)
      throw new Error('math_knowledge_enrichment_tools_changed');
    const manifest = path.join(outputDirectory, 'manifest.json'); writeMathJsonDurable(manifest, result, 0o400);
    return result;
  } finally { fs.rmSync(temporary, { recursive: true, force: true }); }
}
