import { mathDigest } from './mathRuntimeIo';

/** Project declarations in the elaborated type and proof, including implicit and transitive uses. */
export type LeanDeclarationReferences = {
  statement: { name: string; file: string }[];
  proof: { name: string; file: string }[];
};

type ReferenceModule = Readonly<{ module: string; file: string }>;
export type LeanReferenceCollectionOptions = Readonly<{
  maxBytes?: number; maxReferences?: number; fuel?: number;
  expectedTheoremName?: string; expectedModules?: readonly ReferenceModule[];
}>;
export type LeanReferenceFailureReason = 'missing-report' | 'ambiguous-report' | 'malformed-report' | 'identity-mismatch' |
  'legacy-unknown' | 'invalid-reference' | 'traversal-budget-exhausted' | 'reference-count-limit' | 'output-byte-limit' | 'proof-unavailable';
export type LeanReferenceReport = { status: 'complete'; references: LeanDeclarationReferences } | {
  status: 'unavailable'; reason: LeanReferenceFailureReason; phase?: 'statement' | 'proof' | 'report'; observed?: number; limit?: number;
};
const schema = 'theorem-os.lean-references.v2';
const defaultLimits = { maxBytes: 8000, maxReferences: 256, fuel: 200000 };
function limits(options: LeanReferenceCollectionOptions) {
  const value = { maxBytes: options.maxBytes ?? defaultLimits.maxBytes,
    maxReferences: options.maxReferences ?? defaultLimits.maxReferences, fuel: options.fuel ?? defaultLimits.fuel };
  if (!Object.values(value).every(limit => Number.isSafeInteger(limit) && limit >= 0) || value.maxBytes === 0)
    throw new Error('math_lean_reference_limits_invalid');
  return value;
}
const moduleDigest = (modules: readonly ReferenceModule[]) => mathDigest(JSON.stringify(modules.map(item => [item.module, item.file])));

/** Imported library constants cannot refer back to the project: traverse project modules only. */
export function leanReferenceCommands(theoremName: string, modules: readonly ReferenceModule[], marker: string,
  options?: LeanReferenceCollectionOptions): string[] {
  if (options) return leanReferenceCommandsV2(theoremName, modules, marker, options);
  return [
    'run_cmd do',
    '  let env <- Lean.getEnv',
    `  let modules : List (String × String) := [${modules.map(item => `(${JSON.stringify(item.module)}, ${JSON.stringify(item.file)})`).join(', ')}]`,
    '  let collect (expression : Lean.Expr) : Lean.Elab.Command.CommandElabM (Option (List (String × String))) := do',
    '    let mut todo := Lean.Expr.getUsedConstants expression |>.toList',
    '    let mut visited : Lean.NameSet := {}',
    '    let mut result : List (String × String) := []',
    '    let mut fuel := 200000',
    '    while !todo.isEmpty do',
    '      if fuel == 0 then return none',
    '      fuel := fuel - 1',
    '      let name := todo.head!',
    '      todo := todo.tail!',
    '      if !visited.contains name then',
    '        visited := visited.insert name',
    '        let moduleName := match env.getModuleIdxFor? name with',
    '          | some index => env.header.moduleNames[index.toNat]!.toString',
    '          | none => ""',
    '        if let some entry := modules.find? (fun entry => entry.1 == moduleName) then',
    '          result := (name.toString, entry.2) :: result',
    '          if let some info := env.find? name then',
    '            todo := (Lean.Expr.getUsedConstants info.type).toList ++ todo',
    '            if let some value := info.value? (allowOpaque := true) then',
    '              todo := (Lean.Expr.getUsedConstants value).toList ++ todo',
    '    return some result',
    `  let root <- Lean.getConstInfo (${JSON.stringify(theoremName)}.toName)`,
    '  let statement <- collect root.type',
    '  let proof <- match root.value? (allowOpaque := true) with',
    '    | some value => collect value',
    '    | none => pure none',
    '  let report := match statement, proof with',
    '    | some statement, some proof => (Lean.toJson (statement, proof)).compress',
    '    | _, _ => "null"',
    `  Lean.logInfo m!"${marker}{if report.utf8ByteSize <= 8000 then report else "null"}"`,
  ];
}

/** Explicit collection keeps failures distinct and counts unique visited constants, rather than repeated edges. */
function leanReferenceCommandsV2(theoremName: string, modules: readonly ReferenceModule[], marker: string,
  options: LeanReferenceCollectionOptions): string[] {
  const bound = limits(options);
  return [
    'run_cmd do',
    '  let env <- Lean.getEnv',
    `  let modules : List (String × String) := [${modules.map(item => `(${JSON.stringify(item.module)}, ${JSON.stringify(item.file)})`).join(', ')}]`,
    `  let header := [("schema", Lean.toJson ${JSON.stringify(schema)}), ("theoremName", Lean.toJson ${JSON.stringify(theoremName)}),`,
    `    ("moduleDigest", Lean.toJson ${JSON.stringify(moduleDigest(modules))}),`,
    `    ("limits", Lean.Json.mkObj [("maxBytes", Lean.toJson (${bound.maxBytes} : Nat)), ("maxReferences", Lean.toJson (${bound.maxReferences} : Nat)), ("fuel", Lean.toJson (${bound.fuel} : Nat))])]`,
    '  let unavailable (reason phase : String) (observed limit : Nat) := Lean.Json.mkObj (header ++',
    '    [("complete", Lean.toJson false), ("reason", Lean.toJson reason), ("phase", Lean.toJson phase),',
    '      ("observed", Lean.toJson observed), ("limit", Lean.toJson limit)])',
    '  let collect (expression : Lean.Expr) : Lean.Elab.Command.CommandElabM (Except (String × Nat × Nat) (List (String × String))) := do',
    '    let mut todo := Lean.Expr.getUsedConstants expression |>.toList',
    '    let mut visited : Lean.NameSet := {}',
    '    let mut result : List (String × String) := []',
    '    let mut steps := 0',
    '    let mut count := 0',
    '    while !todo.isEmpty do',
    '      let name := todo.head!',
    '      todo := todo.tail!',
    '      if !visited.contains name then',
    `        if steps >= ${bound.fuel} then return .error ("traversal-budget-exhausted", steps + 1, ${bound.fuel})`,
    '        steps := steps + 1',
    '        visited := visited.insert name',
    '        let moduleName := match env.getModuleIdxFor? name with',
    '          | some index => env.header.moduleNames[index.toNat]!.toString',
    '          | none => ""',
    '        if let some entry := modules.find? (fun entry => entry.1 == moduleName) then',
    `          if count >= ${bound.maxReferences} then return .error ("reference-count-limit", count + 1, ${bound.maxReferences})`,
    '          count := count + 1',
    '          result := (name.toString, entry.2) :: result',
    '          if let some info := env.find? name then',
    '            todo := (Lean.Expr.getUsedConstants info.type).toList ++ todo',
    '            if let some value := info.value? (allowOpaque := true) then',
    '              todo := (Lean.Expr.getUsedConstants value).toList ++ todo',
    '    return .ok result',
    `  let root <- Lean.getConstInfo (${JSON.stringify(theoremName)}.toName)`,
    '  let statement <- collect root.type',
    '  let proof <- match root.value? (allowOpaque := true) with',
    '    | some value => collect value',
    '    | none => pure (.error ("proof-unavailable", 0, 0))',
    '  let report := match statement, proof with',
    '    | .ok statement, .ok proof => Lean.Json.mkObj (header ++',
    '      [("complete", Lean.toJson true), ("references", Lean.toJson (statement, proof))])',
    '    | .error (reason, observed, limit), _ => unavailable reason "statement" observed limit',
    '    | _, .error (reason, observed, limit) => unavailable reason "proof" observed limit',
    '  let report := report.compress',
    `  let report := if report.utf8ByteSize <= ${bound.maxBytes} then report else`,
    `    (unavailable "output-byte-limit" "report" report.utf8ByteSize ${bound.maxBytes}).compress`,
    `  Lean.logInfo m!"${marker}{report}"`,
  ];
}

/** An absent, oversized or malformed report is unknown, never an empty dependency set. */
export function parseLeanReferences(stdout: string, marker: string, files: readonly string[],
  options?: LeanReferenceCollectionOptions): LeanDeclarationReferences | undefined {
  const report = parseLeanReferenceReport(stdout, marker, files, options);
  return report.status === 'complete' ? report.references : undefined;
}

/** Only a complete, valid report yields references; a bounded traversal never supplies a partial dependency set. */
export function parseLeanReferenceReport(stdout: string, marker: string, files: readonly string[],
  options: LeanReferenceCollectionOptions = {}): LeanReferenceReport {
  const bound = limits(options);
  const unavailable = (reason: LeanReferenceFailureReason): LeanReferenceReport => ({ status: 'unavailable', reason });
  const lines = stdout.split('\n').flatMap(line => {
    try {
      const value = JSON.parse(line);
      if (value && typeof value === 'object') {
        if (typeof value.data === 'string') return value.data.split('\n');
        if (typeof value.message === 'string') return value.message.split('\n');
      }
    } catch { /* Rendered Lean diagnostics need no wrapper. */ }
    return [line];
  }).filter(line => line.includes(marker));
  if (lines.length !== 1) return unavailable(lines.length ? 'ambiguous-report' : 'missing-report');
  const text = lines[0].slice(lines[0].indexOf(marker) + marker.length);
  if (Buffer.byteLength(text) > bound.maxBytes) return { status: 'unavailable', reason: 'output-byte-limit',
    phase: 'report', observed: Buffer.byteLength(text), limit: bound.maxBytes };
  try {
    let value: unknown = JSON.parse(text);
    if (value === null) return unavailable('legacy-unknown');
    if (value && typeof value === 'object' && !Array.isArray(value)) {
      const report = value as Record<string, unknown>;
      if (report.schema !== schema || typeof report.theoremName !== 'string' || !report.theoremName || report.theoremName.length > 1000 ||
          typeof report.moduleDigest !== 'string' || !/^[a-f0-9]{64}$/u.test(report.moduleDigest) ||
          !report.limits || typeof report.limits !== 'object' || Array.isArray(report.limits)) return unavailable('malformed-report');
      const recordedLimits = report.limits as Record<string, unknown>;
      if (recordedLimits.maxBytes !== bound.maxBytes || recordedLimits.maxReferences !== bound.maxReferences || recordedLimits.fuel !== bound.fuel ||
          options.expectedTheoremName !== undefined && report.theoremName !== options.expectedTheoremName ||
          options.expectedModules !== undefined && report.moduleDigest !== moduleDigest(options.expectedModules)) return unavailable('identity-mismatch');
      if (report.complete === false) {
        if ('references' in report || !['statement', 'proof', 'report'].includes(report.phase as string) ||
            !Number.isSafeInteger(report.observed) || (report.observed as number) < 0 ||
            !Number.isSafeInteger(report.limit) || (report.limit as number) < 0) return unavailable('malformed-report');
        const valid = report.reason === 'traversal-budget-exhausted' && report.phase !== 'report' && report.limit === bound.fuel ||
          report.reason === 'reference-count-limit' && report.phase !== 'report' && report.limit === bound.maxReferences ||
          report.reason === 'output-byte-limit' && report.phase === 'report' && report.limit === bound.maxBytes;
        const proofUnavailable = report.reason === 'proof-unavailable' && report.phase === 'proof' && report.limit === 0 && report.observed === 0;
        if (!proofUnavailable && (!valid || (report.observed as number) <= (report.limit as number))) return unavailable('malformed-report');
        return { status: 'unavailable', reason: report.reason as LeanReferenceFailureReason,
          phase: report.phase as 'statement' | 'proof' | 'report', observed: report.observed as number, limit: report.limit as number };
      }
      if (report.complete !== true) return unavailable('malformed-report');
      value = report.references;
    } else if (options.expectedTheoremName !== undefined || options.expectedModules !== undefined) return unavailable('identity-mismatch');
    if (!Array.isArray(value) || value.length !== 2 || !value.every(Array.isArray)) return unavailable('malformed-report');
    const allowedFiles = new Set(files);
    for (let index = 0; index < value.length; index++) {
      const items = value[index];
      if (items.length > bound.maxReferences) return { status: 'unavailable', reason: 'reference-count-limit',
        phase: index === 0 ? 'statement' : 'proof', observed: items.length, limit: bound.maxReferences };
      if (!items.every((item: unknown) => Array.isArray(item) && item.length === 2 && typeof item[0] === 'string' && item[0].length > 0 &&
          item[0].length <= 1000 && typeof item[1] === 'string' && allowedFiles.has(item[1]))) return unavailable('invalid-reference');
    }
    const read = (items: string[][]) => [...new Map(items.map(([name, file]) => [name + '\0' + file, { name, file }])).values()]
      .sort((a, b) => a.file.localeCompare(b.file) || a.name.localeCompare(b.name));
    return { status: 'complete', references: { statement: read(value[0]), proof: read(value[1]) } };
  } catch { return unavailable('malformed-report'); }
}
