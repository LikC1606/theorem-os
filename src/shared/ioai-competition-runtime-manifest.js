const { spawnSync } = require('node:child_process');
const { createHash } = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');

const IOAI_COMPETITION_RUNTIME_MANIFEST_SCHEMA =
  'deepscientist.ioai.competition.runtime-manifest.v1';
const IOAI_COMPETITION_RUNTIME_MANIFEST_FILENAME =
  'ioai-competition-runtime-manifest.json';

class IoaiCompetitionRuntimeMismatchError extends Error {
  constructor(reason, message, details = {}) {
    super(message);
    this.name = 'IoaiCompetitionRuntimeMismatchError';
    this.code = 'engine_protocol_mismatch';
    this.reason = reason;
    this.details = details;
  }
}

function sha256File(filePath) {
  return createHash('sha256').update(fs.readFileSync(filePath)).digest('hex');
}

function hashEngineSourceTree(engineRoot) {
  const sourceRoot = path.join(engineRoot, 'src');
  const roots = [path.join(engineRoot, 'pyproject.toml'), sourceRoot];
  const files = roots.flatMap((entry) => collectFiles(entry, engineRoot)).sort();
  const hash = createHash('sha256');
  for (const relativePath of files) {
    hash.update(relativePath.replaceAll(path.sep, '/'));
    hash.update('\0');
    hash.update(fs.readFileSync(path.join(engineRoot, relativePath)));
    hash.update('\0');
  }
  return hash.digest('hex');
}

function collectFiles(target, root) {
  const stat = fs.statSync(target);
  if (stat.isFile()) return [path.relative(root, target)];
  return fs
    .readdirSync(target, { withFileTypes: true })
    .filter((entry) => entry.name !== '__pycache__' && entry.name !== '.pytest_cache')
    .flatMap((entry) => {
      if (entry.isFile() && entry.name.endsWith('.pyc')) return [];
      return collectFiles(path.join(target, entry.name), root);
    });
}

function readEngineVersion(engineRoot) {
  const pyproject = fs.readFileSync(path.join(engineRoot, 'pyproject.toml'), 'utf8');
  const project = pyproject.match(/\[project\][\s\S]*?\nversion\s*=\s*"([^"]+)"/u);
  if (!project) throw new Error('IOAI engine version is missing from pyproject.toml');
  return project[1];
}

function readProtocolVersion(projectRoot) {
  const source = fs.readFileSync(
    path.join(projectRoot, 'packages', 'desktop', 'src', 'process', 'competition', 'protocol.ts'),
    'utf8'
  );
  const match = source.match(/IOAI_ENGINE_PROTOCOL_VERSION\s*=\s*(\d+)/u);
  if (!match) throw new Error('IOAI engine protocol version is missing from protocol.ts');
  return Number(match[1]);
}

function discoverBuildPythonIdentity(env = process.env, platform = process.platform) {
  const configured = env.DEEPSCIENTIST_IOAI_PYTHON?.trim();
  const candidates = [
    ...(configured ? [{ command: configured, args: [] }] : []),
    ...(platform === 'win32' ? [{ command: 'py', args: ['-3'] }] : []),
    { command: platform === 'win32' ? 'python' : 'python3', args: [] },
    ...(platform === 'win32' ? [] : [{ command: 'python', args: [] }]),
  ];
  for (const candidate of candidates) {
    const result = spawnSync(
      candidate.command,
      [
        ...candidate.args,
        '-B',
        '-c',
        'import json, platform, sys; print(json.dumps({"executable": sys.executable, "version": platform.python_version()}))',
      ],
      { encoding: 'utf8', env, shell: false, windowsHide: true, timeout: 3000 }
    );
    if (result.status !== 0) continue;
    try {
      const identity = JSON.parse(result.stdout.trim());
      if (typeof identity.executable === 'string' && typeof identity.version === 'string') return identity;
    } catch {
      // Try the next portable Python candidate.
    }
  }
  return { executable: null, version: null };
}

function generateIoaiCompetitionRuntimeManifest({ projectRoot, bundlePath, manifestPath }) {
  const engineRoot = path.join(projectRoot, 'packages', 'ioai-competition-engine');
  const packageJson = JSON.parse(fs.readFileSync(path.join(projectRoot, 'package.json'), 'utf8'));
  const manifest = {
    schema: IOAI_COMPETITION_RUNTIME_MANIFEST_SCHEMA,
    protocol_version: readProtocolVersion(projectRoot),
    deepscientist_version: packageJson.version,
    engine: {
      name: 'deepscientist-ioai-engine',
      version: readEngineVersion(engineRoot),
      source_tree_sha256: hashEngineSourceTree(engineRoot),
    },
    mcp: {
      bundle_sha256: sha256File(bundlePath),
    },
    python: {
      requirement: '>=3.11',
      build: discoverBuildPythonIdentity(),
    },
  };
  fs.writeFileSync(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`, 'utf8');
  return manifest;
}

function verifyIoaiCompetitionRuntimeManifest({
  manifestPath,
  bundlePath,
  engineRoot,
  expectedProtocolVersion,
  expectedDeepScientistVersion,
  expectedEngineVersion,
  python,
}) {
  let manifest;
  try {
    manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
  } catch (error) {
    throw mismatch('runtime_manifest_invalid', 'IOAI runtime manifest is missing or invalid', {
      manifest_path: manifestPath,
      cause: error instanceof Error ? error.message : String(error),
    });
  }
  if (manifest?.schema !== IOAI_COMPETITION_RUNTIME_MANIFEST_SCHEMA) {
    throw mismatch('runtime_manifest_schema_mismatch', 'IOAI runtime manifest schema does not match');
  }
  assertMatch('protocol_version_mismatch', manifest.protocol_version, expectedProtocolVersion);
  assertMatch('deepscientist_version_mismatch', manifest.deepscientist_version, expectedDeepScientistVersion);
  assertMatch('engine_version_mismatch', manifest.engine?.version, expectedEngineVersion);

  const bundleSha256 = checkedHash(() => sha256File(bundlePath), 'mcp_bundle_unreadable');
  assertMatch('mcp_bundle_hash_mismatch', manifest.mcp?.bundle_sha256, bundleSha256);
  const engineSourceTreeSha256 = checkedHash(
    () => hashEngineSourceTree(engineRoot),
    'engine_source_tree_unreadable'
  );
  assertMatch(
    'engine_source_tree_hash_mismatch',
    manifest.engine?.source_tree_sha256,
    engineSourceTreeSha256
  );
  if (
    typeof python?.executable !== 'string' ||
    python.executable.length === 0 ||
    typeof python?.version !== 'string' ||
    !isSupportedPythonVersion(python.version)
  ) {
    throw mismatch('python_runtime_mismatch', 'IOAI runtime requires Python 3.11 or newer', {
      python,
    });
  }

  const identity = {
    schema: IOAI_COMPETITION_RUNTIME_MANIFEST_SCHEMA,
    manifest_sha256: sha256File(manifestPath),
    protocol_version: expectedProtocolVersion,
    deepscientist_version: expectedDeepScientistVersion,
    engine: {
      name: 'deepscientist-ioai-engine',
      version: expectedEngineVersion,
      source_tree_sha256: engineSourceTreeSha256,
    },
    mcp: { bundle_sha256: bundleSha256 },
    python: { executable: python.executable, version: python.version },
  };
  return {
    ...identity,
    startup_fingerprint: createHash('sha256').update(JSON.stringify(identity)).digest('hex'),
  };
}

function checkedHash(operation, reason) {
  try {
    return operation();
  } catch (error) {
    throw mismatch(reason, 'IOAI runtime component could not be hashed', {
      cause: error instanceof Error ? error.message : String(error),
    });
  }
}

function assertMatch(reason, expected, actual) {
  if (expected === actual) return;
  throw mismatch(reason, 'IOAI runtime component does not match its immutable manifest', {
    expected,
    actual,
  });
}

function isSupportedPythonVersion(value) {
  const match = /^(\d+)\.(\d+)(?:\.|$)/u.exec(value);
  if (!match) return false;
  const major = Number(match[1]);
  const minor = Number(match[2]);
  return major > 3 || (major === 3 && minor >= 11);
}

function mismatch(reason, message, details) {
  return new IoaiCompetitionRuntimeMismatchError(reason, message, details);
}

module.exports = {
  IOAI_COMPETITION_RUNTIME_MANIFEST_FILENAME,
  IOAI_COMPETITION_RUNTIME_MANIFEST_SCHEMA,
  IoaiCompetitionRuntimeMismatchError,
  discoverBuildPythonIdentity,
  generateIoaiCompetitionRuntimeManifest,
  hashEngineSourceTree,
  sha256File,
  verifyIoaiCompetitionRuntimeManifest,
};
