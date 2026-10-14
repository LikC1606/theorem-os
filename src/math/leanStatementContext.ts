/** Formal meaning exported from Lean's elaborated type, never from a theorem's proof. */
export type LeanStatementContext = {
  type: string;
  constants: { name: string; module: string; type: string; definition?: string }[];
  omitted: string[];
};

/** Follow local definitions and two levels of imported definitions; expose all bounds explicitly. */
export function leanStatementContextCommands(roots: readonly { id: string; name: string }[],
  projectModules: readonly string[], outputFile: string): string {
  return [
    'set_option pp.fullNames true',
    'set_option pp.notation false',
    'set_option pp.proofs false',
    'run_cmd Lean.Elab.Command.liftTermElabM do',
    '  let env <- Lean.getEnv',
    `  let localModules : List String := ${JSON.stringify(projectModules)}`,
    '  let collect (rootName : Lean.Name) : Lean.Elab.Term.TermElabM Lean.Json := do',
      '    let root <- Lean.getConstInfo rootName',
      '    let statement := (<- Lean.Meta.ppExpr root.type).pretty',
      '    if statement.utf8ByteSize > 24000 then throwError "Statement type exceeds its export bound"',
      '    let mut todo := (Lean.Expr.getUsedConstants root.type).toList.map (fun name => (name, 0))',
      '    let mut visited : Lean.NameSet := {}',
      '    let mut constants : Array Lean.Json := #[]',
      '    let mut omitted : Array String := #[]',
      '    let mut bytes := statement.utf8ByteSize',
      '    let mut fuel := 10000',
      '    while !todo.isEmpty && fuel > 0 && constants.size < 256 do',
      '      fuel := fuel - 1',
      '      let (name, depth) := todo.head!',
      '      todo := todo.tail!',
      '      if !visited.contains name then',
      '        visited := visited.insert name',
      '        let info <- Lean.getConstInfo name',
      '        let moduleName := match env.getModuleIdxFor? name with',
      '          | some index => env.header.moduleNames[index.toNat]!.toString',
      '          | none => ""',
      '        let isLocal := moduleName.isEmpty || localModules.contains moduleName',
      '        let value <- match info with',
      '          | .defnInfo definition => do',
      '            if (<- Lean.Meta.isProp info.type) then pure none else pure (some definition.value)',
      '          | _ => pure none',
      '        if isLocal then',
      '          todo := todo ++ (Lean.Expr.getUsedConstants info.type).toList.map (fun name => (name, 0))',
      '        else',
      '          let type := (<- Lean.Meta.ppExpr info.type).pretty',
      '          let definition <- match value with',
      '            | some expression => pure (some (<- Lean.Meta.ppExpr expression).pretty)',
      '            | none => pure none',
      '          let mut fields := [("name", Lean.toJson name.toString), ("module", Lean.toJson moduleName), ("type", Lean.toJson type)]',
      '          if let some text := definition then',
      '            if text.utf8ByteSize <= 12000 then fields := fields ++ [("definition", Lean.toJson text)]',
      '            else if omitted.size < 256 then omitted := omitted.push name.toString',
      '          let record := Lean.Json.mkObj fields',
      '          let size := record.compress.utf8ByteSize',
      '          if constants.size < 256 && type.utf8ByteSize <= 8000 && bytes + size <= 240000 then',
      '            constants := constants.push record',
      '            bytes := bytes + size',
      '          else if omitted.size < 256 then omitted := omitted.push name.toString',
      '        if let some expression := value then',
      '          if isLocal || depth < 2 then',
      '            todo := todo ++ (Lean.Expr.getUsedConstants expression).toList.map (fun name => (name, if isLocal then 0 else depth + 1))',
      '    if !todo.isEmpty then omitted := omitted.push "dependency traversal bound reached"',
    '    return Lean.Json.mkObj [("type", Lean.toJson statement), ("constants", Lean.toJson constants), ("omitted", Lean.toJson omitted)]',
    '  let mut reports : Array Lean.Json := #[]',
    ...roots.flatMap(root => [
      `  let context <- collect (${JSON.stringify(root.name)}.toName)`,
      `  reports := reports.push (Lean.Json.mkObj [("id", Lean.toJson ${JSON.stringify(root.id)}), ("context", context)])`,
    ]),
    '  let report := (Lean.toJson reports).compress',
    '  if report.utf8ByteSize > 4000000 then throwError "Statement context exceeds its export bound"',
    `  Lean.Core.liftIOCore <| IO.FS.writeFile ${JSON.stringify(outputFile)} report`,
  ].join('\n');
}

export function parseLeanStatementContexts(text: string, ids: readonly string[]): Map<string, LeanStatementContext> {
  const invalid = () => { throw new Error('math_statement_elaboration_invalid'); };
  if (Buffer.byteLength(text) > 4_000_000) return invalid();
  const reports: unknown = JSON.parse(text);
  if (!Array.isArray(reports) || reports.length !== ids.length) return invalid();
  const contexts = new Map<string, LeanStatementContext>();
  for (const report of reports) {
    const context = report?.context;
    if (!ids.includes(report?.id) || contexts.has(report.id) || !context || typeof context.type !== 'string' ||
        !context.type.trim() || Buffer.byteLength(context.type) > 24000 || !Array.isArray(context.constants) || context.constants.length > 256 ||
        !context.constants.every((item: any) => item && typeof item.name === 'string' && item.name.length <= 1000 &&
          typeof item.module === 'string' && item.module.length <= 1000 && typeof item.type === 'string' && Buffer.byteLength(item.type) <= 8000 &&
          (item.definition === undefined || (typeof item.definition === 'string' && Buffer.byteLength(item.definition) <= 12000))) ||
        !Array.isArray(context.omitted) || context.omitted.length > 257 || !context.omitted.every((item: unknown) => typeof item === 'string' && item.length <= 1000) ||
        Buffer.byteLength(JSON.stringify(context)) > 256000) return invalid();
    contexts.set(report.id, { type: context.type, constants: context.constants, omitted: context.omitted });
  }
  return contexts;
}
