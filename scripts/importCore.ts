#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
const flag = args.indexOf('--bundle');
if (args.includes('--help') || args.includes('-h')) {
  console.log('Usage: deepscientist-math import-core --bundle DIRECTORY\nCopies a native v0.1.50 Core bundle and its managed resources. Credentials and staging files are excluded.');
} else {
  if (flag < 0 || !args[flag + 1]) throw new Error('A prepared Core --bundle DIRECTORY is required');
  const source = fs.realpathSync(args[flag + 1]!);
  const metadata = JSON.parse(fs.readFileSync(path.join(source, 'manifest.json'), 'utf8'));
  if (metadata.platform !== process.platform || metadata.arch !== process.arch || metadata.version !== 'v0.1.50')
    throw new Error('math_core_bundle_platform_or_version_mismatch');
  const target = path.join(root, 'runtime', `${process.platform}-${process.arch}`);
  if (fs.existsSync(target)) throw new Error('math_core_bundle_destination_exists');
  const binary = process.platform === 'win32' ? 'deepscientist-core.exe' : 'deepscientist-core';
  const members = [binary, 'manifest.json', 'managed-resources/manifest.json', 'managed-resources/node', 'managed-resources/acp'];
  const links: { relative: string; targetRelative: string }[] = [];
  const within = (file: string) => file === source || file.startsWith(source + path.sep);
  const inspect = (relative: string): void => {
    const file = path.join(source, relative);
    const stat = fs.lstatSync(file);
    if (stat.isSymbolicLink()) {
      const raw = fs.readlinkSync(file);
      let local = path.resolve(path.dirname(file), raw);
      if (!within(local)) {
        // Historical bundle preparation made absolute links into staging.
        // Accept only the corresponding file already shipped in this bundle.
        const marker = `${path.sep}managed-resources${path.sep}`;
        const index = raw.lastIndexOf(marker);
        if (index < 0) throw new Error('math_core_bundle_link_escapes');
        local = path.join(source, 'managed-resources', raw.slice(index + marker.length));
      }
      if (!within(local) || !within(fs.realpathSync(local))) throw new Error('math_core_bundle_link_escapes');
      links.push({ relative, targetRelative: path.relative(source, fs.realpathSync(local)) });
    } else if (stat.isDirectory()) {
      for (const name of fs.readdirSync(file)) inspect(path.join(relative, name));
    } else if (!stat.isFile()) throw new Error('math_core_bundle_file_invalid');
  };
  for (const member of members) inspect(member);
  fs.mkdirSync(path.dirname(target), { recursive: true });
  const staging = fs.mkdtempSync(path.join(path.dirname(target), '.import-'));
  try {
    for (const member of members) {
      const destination = path.join(staging, member);
      fs.mkdirSync(path.dirname(destination), { recursive: true });
      fs.cpSync(path.join(source, member), destination, {
        recursive: true, verbatimSymlinks: true, mode: fs.constants.COPYFILE_FICLONE,
      });
    }
    for (const link of links) {
      const destination = path.join(staging, link.relative);
      fs.unlinkSync(destination);
      fs.symlinkSync(path.relative(path.dirname(destination), path.join(staging, link.targetRelative)), destination);
    }
    fs.renameSync(staging, target);
  } catch (error) {
    fs.rmSync(staging, { recursive: true, force: true });
    throw error;
  }
  console.log(JSON.stringify({ coreBundle: target, internalLinks: links.length, stagingIncluded: false }));
}
