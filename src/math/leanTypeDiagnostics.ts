import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { inspectLeanDeclarationRegions, leanDeclarationContextCommands } from './leanSource';
import { bindLeanPackages, prepareLeanDiagnosticOverrides, runLeanDiagnostics } from './leanDiagnostics';
import { resolveMathematicsRuntimeEnvironment } from './mathRuntimeEnvironment';
import { resolveMathProofEnvironment } from './mathProofEnvironment';
import { canonicalMathJson, mathDigest, readMathFile, readMathJson, writeMathJsonDurable } from './mathRuntimeIo';
import { assertMathCanonicalPath } from './paths';
import { leanDiagnosticEnvironmentIdentity } from './leanResidualGoals';

/** Parse and elaborate a closed type as data; never splice a requested type into executable Lean commands. */
export function leanTypeDiagnosticCommands(type: string, output: string, application?: string) {
  return ['set_option autoImplicit false', 'set_option pp.fullNames true',
    'run_cmd Lean.Elab.Command.liftTermElabM do',
    `  let parsed <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "term") ${JSON.stringify(type)} with`,
    '    | .ok stx => pure stx', '    | .error message => throwError "{message}"',
    '  let expression <- Lean.Elab.Term.elabType parsed',
    '  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing',
    '  let expression <- Lean.instantiateMVars expression',
    '  if expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then',
    '    throwError "Requested type must be closed without free variables or metavariables"',
    '  let rendered := (<- Lean.Meta.ppExpr expression).pretty',
    '  if rendered.utf8ByteSize > 24000 then throwError "Elaborated type exceeds its export bound"',
    ...(application === undefined ? ['  let report := Lean.Json.mkObj [("type", Lean.toJson rendered)]'] : [
      `  let term <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "term") ${JSON.stringify(application)} with`,
      '    | .ok stx => pure stx', '    | .error message => throwError "{message}"',
      '  let applied <- Lean.Elab.Term.elabTermEnsuringType term expression',
      '  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing',
      '  let applied <- Lean.instantiateMVars applied',
      '  if applied.hasMVar || applied.hasFVar || applied.hasLooseBVars then',
      '    throwError "Application must be closed without free variables or metavariables"',
      '  let constants := applied.getUsedConstants.toList.map Lean.Name.toString',
      '  if constants.contains "sorryAx" then throwError "Application contains an admitted term"',
      '  if constants.length > 4096 then throwError "Application reference export exceeds its bound"',
      '  let report := Lean.Json.mkObj [("type", Lean.toJson rendered), ("constants", Lean.toJson constants)]',
    ]),
    `  Lean.Core.liftIOCore <| IO.FS.writeFile ${JSON.stringify(output)} report.compress`].join('\n');
}

/** The clone and reuse identity must describe the same bytes, module graph and query. */
export function leanTypeDiagnosticProjection(input: {
  files: readonly { file: string; source: string }[];
  modules: readonly { file: string; sourceRoot: string; module: string }[];
  file: string; context: string; type: string; expression?: string;
}) {
  const context = leanDeclarationContextCommands(input.files.find(file => file.file === input.file)!.source, input.context);
  const module = input.modules.find(module => module.file === input.file)!.module;
  if (!/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/u.test(module))
    throw new Error('math_type_diagnostics_module_invalid');
  const files = input.files.map(file => {
    let source = file.source;
    if (file.file.endsWith('.lean') && file.file !== 'lakefile.lean') {
      for (const region of inspectLeanDeclarationRegions(source).reverse())
        if (/^(?:theorem|lemma)\s/u.test(source.slice(region.startOffset, region.bodyOffset)))
          source = source.slice(0, region.bodyOffset) + ' by sorry\n' + source.slice(region.endOffset);
    }
    return { file: file.file, source };
  });
  const query = 'TypeDiagnostic.lean', output = '.lake/type-diagnostic.json';
  const commands = ['import Lean', `import ${module}`, ...context.before,
    leanTypeDiagnosticCommands(input.type, output, input.expression), ...context.after].join('\n') + '\n';
  const digest = mathDigest(canonicalMathJson({ schema: 'theoremos.lean-type-projection.v1',
    modules: input.modules, files: files.map(({ file, source }) => ({ file, digest: mathDigest(source) })), query, commands }));
  return { files, query, output, commands, digest };
}

/** Explicit advisory preflight in a fixed, proof-erased local snapshot. It cannot grant proof acceptance. */
export async function checkLeanType(input: { projectRoot: string; file: string; context: string; type: string; expression?: string;
  env?: NodeJS.ProcessEnv; signal?: AbortSignal; timeoutMs: number; onProgress?: (file: string) => void }) {
  if (!input.type.trim() || Buffer.byteLength(input.type) > 12000 || !input.context.trim() || input.context.length > 1000 ||
      input.expression !== undefined && (!input.expression.trim() || Buffer.byteLength(input.expression) > 12000))
    throw new Error('math_type_diagnostics_input_invalid');
  const project = fs.realpathSync(input.projectRoot);
  const env = resolveMathematicsRuntimeEnvironment(input.env ?? process.env);
  const sealed = resolveMathProofEnvironment(project, env);
  const environment = leanDiagnosticEnvironmentIdentity(project, env);
  assertMathConstructionSources(project, [input.file]);
  const modules = mathLocalModuleBuildOrder(project, input.file);
  const configs = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
  const files = [...modules.map(module => module.file), ...configs.filter(file => fs.existsSync(path.join(project, file)))];
  const snapshot = files.map(file => {
    const source = path.join(project, file); assertMathCanonicalPath(source);
    const read = readMathFile(source, 4_000_000);
    return { file, source: read.bytes.toString('utf8'), digest: mathDigest(read.bytes), identity: read.identity };
  });
  const sourceDigest = mathDigest(canonicalMathJson(snapshot.map(({ file, digest }) => ({ file, digest }))));
  const projection = leanTypeDiagnosticProjection({ files: snapshot, modules,
    file: input.file, context: input.context, type: input.type, expression: input.expression });
  const directory = path.join(project, '.lake', 'type-diagnostics', crypto.randomUUID()), clone = path.join(directory, 'project');
  assertMathCanonicalPath(clone); fs.mkdirSync(clone, { recursive: true, mode: 0o700 });
  for (const file of projection.files) {
    const target = path.join(clone, file.file); assertMathCanonicalPath(target);
    fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 }); fs.writeFileSync(target, file.source, { mode: 0o600 });
  }
  // Recheck the entire original input window after copying; the clone remains fixed during Lean execution.
  for (const file of snapshot) {
    const current = readMathFile(path.join(project, file.file), 4_000_000);
    if (current.identity !== file.identity || mathDigest(current.bytes) !== file.digest) throw new Error('math_type_diagnostics_source_changed');
  }
  const packages = sealed?.packagesRoot ?? path.join(project, '.lake', 'packages');
  if (fs.existsSync(packages)) bindLeanPackages(clone, packages);
  prepareLeanDiagnosticOverrides(clone);
  if (sealed) {
    sealed.verify();
    if (resolveMathProofEnvironment(clone, env)?.identity !== sealed.identity)
      throw new Error('math_type_diagnostics_environment_changed');
  }
  fs.writeFileSync(path.join(clone, projection.query), projection.commands, { mode: 0o600 });
  const diagnostics = await runLeanDiagnostics({ projectRoot: clone, files: [projection.query], env,
    signal: input.signal, timeoutMs: input.timeoutMs, onProgress: input.onProgress });
  // A snapshot can finish after its live consumer or package/tool binding has changed.
  for (const file of snapshot) {
    const current = readMathFile(path.join(project, file.file), 4_000_000);
    if (current.identity !== file.identity || mathDigest(current.bytes) !== file.digest) throw new Error('math_type_diagnostics_source_changed');
  }
  if (canonicalMathJson(mathLocalModuleBuildOrder(project, input.file)) !== canonicalMathJson(modules) ||
      canonicalMathJson(configs.filter(file => fs.existsSync(path.join(project, file)))) !==
        canonicalMathJson(files.filter(file => configs.includes(file))) ||
      canonicalMathJson(leanDiagnosticEnvironmentIdentity(project, env)) !== canonicalMathJson(environment))
    throw new Error('math_type_diagnostics_environment_or_sources_changed');
  sealed?.verify();
  let elaboratedType: string | undefined, constants: string[] | undefined;
  if (diagnostics.exitCode === 0 && !diagnostics.timedOut) {
    const value = readMathJson(path.join(clone, projection.output)) as Record<string, unknown>;
    if (typeof value.type !== 'string' || !value.type.trim() || Buffer.byteLength(value.type) > 24000)
      throw new Error('math_type_diagnostics_export_invalid');
    elaboratedType = value.type;
    if (input.expression !== undefined) {
      if (!Array.isArray(value.constants) || value.constants.length > 4096 ||
          value.constants.some(item => typeof item !== 'string' || item.length > 1000))
        throw new Error('math_type_diagnostics_export_invalid');
      constants = value.constants;
    }
  }
  const evidence = input.expression === undefined ? 'advisory-type-elaboration' : 'advisory-application-elaboration';
  const manifest = { schema: 'theoremos.lean-type-diagnostics.v1', authority: evidence,
    proofAcceptance: 'not-assessed', sourceDigest, projectionDigest: projection.digest, queryDigest: mathDigest(projection.commands),
    files: snapshot.map(({ file, digest }) => ({ file, digest })), context: input.context, requestedType: input.type,
    ...(input.expression !== undefined ? { requestedExpression: input.expression, constants } : {}),
    environment, elaboratedType, diagnostics };
  const artifactFile = path.join(directory, 'manifest.json'); writeMathJsonDurable(artifactFile, manifest);
  return { ...diagnostics, status: elaboratedType ? 'elaborated' as const : 'failed' as const,
    type: elaboratedType, sourceSnapshotDigest: sourceDigest, projectionDigest: projection.digest, context: input.context,
    sourceFiles: snapshot.map(({ file, digest }) => ({ file, digest })), environment,
    ...(input.expression !== undefined ? { expression: input.expression, constants } : {}),
    artifact: { path: path.relative(project, artifactFile).replaceAll(path.sep, '/'), digest: mathDigest(canonicalMathJson(manifest)) },
    diagnosticArtifacts: diagnostics.diagnosticArtifacts.map(reference => ({ ...reference,
      path: path.relative(project, path.join(clone, reference.path)).replaceAll(path.sep, '/') })),
    evidence, proofAcceptance: 'not-assessed' };
}
