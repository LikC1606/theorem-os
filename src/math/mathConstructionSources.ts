import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";

/** Read the Lean header only: comments nest and quoted identifiers are single tokens. */
export function mathConstructionImports(source: string): string[] {
  let offset = 0;
  const next = (): string | undefined => {
    for (;;) {
      while (/\s/u.test(source[offset] ?? '') && offset < source.length) offset++;
      if (source.startsWith('--', offset)) {
        const end = source.indexOf('\n', offset);
        offset = end < 0 ? source.length : end;
      } else if (source.startsWith('/-', offset)) {
        let depth = 1;
        offset += 2;
        while (offset < source.length && depth) {
          if (source.startsWith('/-', offset)) {
            depth++;
            offset += 2;
          } else if (source.startsWith('-/', offset)) {
            depth--;
            offset += 2;
          } else offset++;
        }
        if (depth) throw new Error('math_construction_unclosed_header_comment');
      } else break;
    }
    const token = source
      .slice(offset)
      .match(/^(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\n]+»)(?:\.(?:[\p{L}_][\p{L}\p{M}\p{N}_']*|«[^»\n]+»))*/u)?.[0];
    if (token) offset += token.length;
    return token;
  };
  const imports: string[] = [];
  const boundaries = new Set([
    'import',
    'public',
    'private',
    'meta',
    'namespace',
    'section',
    'end',
    'theorem',
    'lemma',
    'def',
    'example',
    'abbrev',
    'opaque',
    'instance',
    'inductive',
    'structure',
    'class',
    'axiom',
    'constant',
    'variable',
    'universe',
    'open',
    'export',
    'set_option',
    'attribute',
    'noncomputable',
    'unsafe',
    'syntax',
    'macro',
    'elab',
    'notation',
    'infix',
    'infixl',
    'infixr',
    'prefix',
    'postfix',
    'initialize',
    'builtin_initialize',
  ]);
  let token = next();
  while (token === 'prelude' || token === 'module') token = next();
  while (token === 'import' || token === 'public' || token === 'private' || token === 'meta') {
    while (token === 'public' || token === 'private' || token === 'meta') token = next();
    if (token !== 'import') break;
    token = next();
    if (!token || boundaries.has(token)) throw new Error('math_construction_invalid_import');
    while (token && !boundaries.has(token)) {
      imports.push(token);
      token = next();
    }
  }
  return imports;
}

const assertRegularSource = (root: string, relative: string): string => {
  if (!isAllowedMathProofSource(relative)) throw new Error(`math_construction_source_excluded: ${relative}`);
  const file = path.join(root, relative);
  if (fs.realpathSync(file) !== file || !fs.lstatSync(file).isFile())
    throw new Error('math_construction_source_path_invalid');
  return file;
};

function localSourceDirectories(root: string): Set<string> {
  const directories = new Set(['', 'src']);
  const config = path.join(root, 'lakefile.toml');
  if (fs.existsSync(config)) {
    if (fs.realpathSync(config) !== config || !fs.lstatSync(config).isFile())
      throw new Error('math_construction_config_path_invalid');
    const parsed = parseToml(fs.readFileSync(config, 'utf8'));
    for (const library of Array.isArray(parsed.lean_lib) ? parsed.lean_lib : []) {
      if (library && typeof library === 'object' && 'srcDir' in library && typeof library.srcDir === 'string') {
        const directory = library.srcDir;
        if (directory === '.') directories.add('');
        else if (
          !path.isAbsolute(directory) &&
          directory.split(/[\\/]/u).every((part) => part && part !== '..' && part !== '.')
        )
          directories.add(directory);
        else throw new Error('math_construction_source_directory_invalid');
      }
    }
  }
  return directories;
}

/** Validate paths before reading them, including the transitive project-local import closure. */
export function assertMathConstructionSources(rootInput: string, files: readonly string[]): void {
  for (const file of files)
    if (!isAllowedMathProofSource(file)) throw new Error(`math_construction_source_excluded: ${file}`);
  const root = fs.realpathSync(rootInput);
  const directories = localSourceDirectories(root);
  const queue = [...files];
  const visited = new Set<string>();
  for (let index = 0; index < queue.length; index++) {
    const relative = queue[index]!;
    if (visited.has(relative)) continue;
    visited.add(relative);
    const file = assertRegularSource(root, relative);
    const source = fs.readFileSync(file, 'utf8');
    for (const name of mathConstructionImports(source)) {
      const moduleFile =
        (name.match(/«[^»]+»|[^.]+/gu) ?? []).map((part) => part.replaceAll('«', '').replaceAll('»', '')).join('/') +
        '.lean';
      if (!isAllowedMathProofSource(moduleFile)) throw new Error(`math_construction_import_excluded: ${name}`);
      for (const directory of directories) {
        const candidate = directory ? `${directory}/${moduleFile}` : moduleFile;
        if (fs.existsSync(path.join(root, candidate))) queue.push(candidate);
      }
    }
  }
}

/** Compile only the project-local import closure, reusing frozen package artifacts. */
export function mathLocalModuleBuildOrder(rootInput: string, relative: string): { file: string; sourceRoot: string; module: string }[] {
  const root = fs.realpathSync(rootInput);
  const directories = [...localSourceDirectories(root)];
  const ordered: { file: string; sourceRoot: string; module: string }[] = [];
  const visited = new Set<string>();
  const visiting = new Set<string>();
  const visit = (file: string, sourceRoot: string): void => {
    if (visited.has(file)) return;
    if (visiting.has(file)) throw new Error('math_local_module_import_cycle');
    const absolute = path.resolve(root, file);
    if (path.relative(root, absolute).startsWith('..') || !file.endsWith('.lean') ||
        fs.realpathSync(absolute) !== absolute || !fs.lstatSync(absolute).isFile())
      throw new Error('math_local_module_source_invalid');
    visiting.add(file);
    for (const name of mathConstructionImports(fs.readFileSync(absolute, 'utf8'))) {
      const parts = (name.match(/«[^»]+»|[^.]+/gu) ?? []).map(part => part.replaceAll('«', '').replaceAll('»', ''));
      if (parts.some(part => !part || part === '.' || part === '..' || /[/\\\0]/u.test(part)))
        throw new Error('math_local_module_import_invalid');
      const moduleFile = `${parts.join('/')}.lean`;
      for (const directory of directories) {
        const candidate = directory ? `${directory}/${moduleFile}` : moduleFile;
        if (fs.existsSync(path.join(root, candidate))) { visit(candidate, directory); break; }
      }
    }
    visiting.delete(file);
    visited.add(file);
    ordered.push({ file, sourceRoot: sourceRoot || '.',
      module: path.posix.relative(sourceRoot || '.', file).replace(/\.lean$/u, '').replaceAll('/', '.') });
  };
  const sourceRoot = directories.filter(directory => directory && relative.startsWith(`${directory}/`))
    .sort((a, b) => b.length - a.length)[0] || '';
  visit(relative, sourceRoot);
  return ordered;
}

/** Called only on the disposable verifier checkout, before it is mounted for Lean. */
export function pruneMathConstructionCheckout(checkoutRoot: string, projectRoot: string): void {
  const directories = [checkoutRoot];
  for (let index = 0; index < directories.length; index++) {
    const directory = directories[index]!;
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      if (entry.name === '.git' || entry.name === '.lake' || entry.isSymbolicLink()) continue;
      const file = path.join(directory, entry.name);
      if (entry.isDirectory()) directories.push(file);
      else if (entry.isFile() && entry.name.endsWith('.lean') && entry.name !== 'lakefile.lean') {
        const projectRelative = path.relative(projectRoot, file);
        const relative =
          projectRelative === '..' || projectRelative.startsWith(`..${path.sep}`)
            ? path.relative(checkoutRoot, file)
            : projectRelative;
        if (!isAllowedMathProofSource(relative.replaceAll(path.sep, '/'))) fs.unlinkSync(file);
      }
    }
  }
}
