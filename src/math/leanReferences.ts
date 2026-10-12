/** Project declarations in the elaborated type and proof, including implicit and transitive uses. */
export type LeanDeclarationReferences = {
  statement: { name: string; file: string }[];
  proof: { name: string; file: string }[];
};

/** Imported library constants cannot refer back to the project: traverse project modules only. */
export function leanReferenceCommands(theoremName: string, modules: readonly { module: string; file: string }[], marker: string): string[] {
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

/** An absent, oversized or malformed report is unknown, never an empty dependency set. */
export function parseLeanReferences(stdout: string, marker: string, files: readonly string[]): LeanDeclarationReferences | undefined {
  const lines = stdout.split('\n').filter(line => line.includes(marker));
  if (lines.length !== 1) return;
  const text = lines[0].slice(lines[0].indexOf(marker) + marker.length);
  if (Buffer.byteLength(text) > 8000) return;
  try {
    const value: unknown = JSON.parse(text);
    if (!Array.isArray(value) || value.length !== 2 || !value.every(items => Array.isArray(items) && items.length <= 256 &&
      items.every(item => Array.isArray(item) && item.length === 2 && typeof item[0] === 'string' && item[0].length > 0 &&
        item[0].length <= 1000 && typeof item[1] === 'string' && files.includes(item[1])))) return;
    const read = (items: string[][]) => [...new Map(items.map(([name, file]) => [name + '\0' + file, { name, file }])).values()]
      .sort((a, b) => a.file.localeCompare(b.file) || a.name.localeCompare(b.name));
    return { statement: read(value[0]), proof: read(value[1]) };
  } catch { return; }
}
