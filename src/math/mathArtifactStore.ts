import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import type {
  MathArtifactManifestEntry,
  MathArtifactReadRequest,
  MathArtifactReadResponse,
} from "../common/types/team/mathRuntimeContracts";
import { assertMathCanonicalPath } from "./mathRunBinding";
import { normalizeMathArtifactRead, parseMathArtifactReference } from "./mathPublicWire";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  syncMathDirectory,
  withMathRuntimeLease,
  writeMathJsonDurable,
  type MathLease,
} from "./mathRuntimeIo";

const id = z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u);
const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const count = z.number().int().nonnegative().safe();
const entrySchema = z
  .object({
    artifactId: id,
    runId: id,
    assignmentId: id.optional(),
    kind: z.enum(['compiler', 'evidence', 'diagnostic', 'evaluator']),
    sha256: digest,
    bytes: count,
    originalBytes: count.optional(),
    mediaType: z.string().min(1),
    createdAt: z.string().datetime(),
    sensitivity: z.enum(['solver-visible', 'runtime-only', 'evaluator-private']),
    truncated: z.boolean(),
  })
  .strict();
const manifestSchema = z
  .object({
    schema: z.literal('deepscientist.math.artifacts.v1'),
    runId: id,
    revision: count,
    entries: z.record(entrySchema),
    grants: z.record(z.array(id)),
  })
  .strict();
type Manifest = {
  schema: 'deepscientist.math.artifacts.v1';
  runId: string;
  revision: number;
  entries: Record<string, MathArtifactManifestEntry>;
  grants: Record<string, string[]>;
};
type Intent = {
  schema: 'deepscientist.math.artifact-intent.v1';
  state: 'prepared' | 'object_published' | 'manifest_committed';
  expectedManifestRevision: number;
  tempName: string;
  entry: MathArtifactManifestEntry;
  grants: string[];
};
const intentSchema = z
  .object({
    schema: z.literal('deepscientist.math.artifact-intent.v1'),
    state: z.enum(['prepared', 'object_published', 'manifest_committed']),
    expectedManifestRevision: count,
    tempName: z.string().regex(/^\.[A-Za-z0-9_-]+\.tmp$/u),
    entry: entrySchema,
    grants: z.array(id),
  })
  .strict();
const ledgerSchema = z
  .object({
    schema: z.literal('deepscientist.math.artifact-gc.v1'),
    runId: id,
    terminalAt: count,
    retainUntil: count,
    pin: z.boolean(),
    state: z.enum(['retained', 'eligible', 'deleting', 'deleted']),
    manifestDigest: digest,
  })
  .strict();
type Ledger = {
  schema: 'deepscientist.math.artifact-gc.v1';
  runId: string;
  terminalAt: number;
  retainUntil: number;
  pin: boolean;
  state: 'retained' | 'eligible' | 'deleting' | 'deleted';
  manifestDigest: string;
};
export type MathArtifactAccess = Readonly<{
  role: 'lead' | 'worker';
  assignmentId?: string;
  grants?: ReadonlySet<string>;
}>;
type PublishInput = Readonly<{
  artifactId: string;
  assignmentId?: string;
  kind: MathArtifactManifestEntry['kind'];
  sensitivity: MathArtifactManifestEntry['sensitivity'];
  mediaType: string;
  grants?: readonly string[];
}>;
type Reader = {
  fd: number;
  stat: fs.BigIntStats;
  release: () => Promise<void>;
  lease: MathLease;
  timer?: NodeJS.Timeout;
};
const MAX_CACHED_READERS = 32;

export class MathArtifactError extends Error {
  constructor(readonly code: 'not_found' | 'unauthorized' | 'integrity' | 'invalid' | 'conflict') {
    super(`math_artifact_${code}`);
    this.name = 'MathArtifactError';
  }
}

export class MathArtifactStore {
  readonly artifactRoot: string;
  private readonly objects: string;
  private readonly intents: string;
  private readonly completed: string;
  private readonly manifestFile: string;
  private readonly ledgerFile: string;
  private readonly readers = new Map<string, Reader>();
  private readonly openingReaders = new Map<string, Promise<Reader>>();
  private readerQueue: Promise<void> = Promise.resolve();
  private manifestCache?: { value: Manifest; stat: fs.BigIntStats };

  constructor(
    private readonly options: Readonly<{
      runRoot: string;
      runId: string;
      flockExecutable: string;
      now?: () => number;
      onHash?: () => void;
      fault?: (phase: string) => void;
    }>
  ) {
    id.parse(options.runId);
    assertMathCanonicalPath(options.runRoot);
    if (path.basename(options.runRoot) !== options.runId || path.basename(path.dirname(options.runRoot)) !== 'runs')
      throw new MathArtifactError('invalid');
    this.artifactRoot = path.join(options.runRoot, 'artifacts');
    this.objects = path.join(this.artifactRoot, 'objects');
    this.intents = path.join(this.artifactRoot, 'intents');
    this.completed = path.join(this.intents, 'completed');
    this.manifestFile = path.join(this.artifactRoot, 'manifest.v1.json');
    this.ledgerFile = path.join(options.runRoot, 'artifact-gc.json');
  }

  private now(): number {
    return this.options.now?.() ?? Date.now();
  }
  private lock(name: string, shared = false) {
    return {
      lockPath: path.join(this.options.runRoot, name),
      flockExecutable: this.options.flockExecutable,
      shared,
    };
  }
  private assertRoot(): void {
    assertMathCanonicalPath(this.options.runRoot);
    if ((fs.statSync(this.options.runRoot).mode & 0o777) !== 0o700) throw new MathArtifactError('integrity');
  }
  private ledger(): Ledger | undefined {
    try {
      fs.lstatSync(this.ledgerFile);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') return undefined;
      throw new MathArtifactError('integrity');
    }
    try {
      const parsed = ledgerSchema.safeParse(readMathJson(this.ledgerFile));
      if (!parsed.success || parsed.data.runId !== this.options.runId) throw new MathArtifactError('integrity');
      return parsed.data as Ledger;
    } catch {
      throw new MathArtifactError('integrity');
    }
  }
  private manifest(): Manifest {
    assertMathCanonicalPath(this.manifestFile);
    const stat = fs.lstatSync(this.manifestFile, { bigint: true });
    const cached = this.manifestCache;
    if (
      cached &&
      stat.dev === cached.stat.dev &&
      stat.ino === cached.stat.ino &&
      stat.size === cached.stat.size &&
      stat.mtimeNs === cached.stat.mtimeNs &&
      stat.ctimeNs === cached.stat.ctimeNs
    )
      return cached.value;
    const parsed = manifestSchema.safeParse(readMathJson(this.manifestFile));
    if (!parsed.success || parsed.data.runId !== this.options.runId) throw new MathArtifactError('integrity');
    const manifest = parsed.data as Manifest;
    for (const [key, entry] of Object.entries(manifest.entries)) {
      if (key !== entry.artifactId || entry.runId !== this.options.runId) throw new MathArtifactError('integrity');
    }
    for (const [key, targets] of Object.entries(manifest.grants)) {
      if (
        !manifest.entries[key] ||
        new Set(targets).size !== targets.length ||
        targets.some((target) => !manifest.entries[target] || manifest.entries[target].sensitivity !== 'solver-visible')
      )
        throw new MathArtifactError('integrity');
    }
    const after = fs.lstatSync(this.manifestFile, { bigint: true });
    if (
      stat.dev !== after.dev ||
      stat.ino !== after.ino ||
      stat.size !== after.size ||
      stat.mtimeNs !== after.mtimeNs ||
      stat.ctimeNs !== after.ctimeNs
    )
      throw new MathArtifactError('integrity');
    this.manifestCache = { value: manifest, stat };
    return manifest;
  }

  async initialize(): Promise<void> {
    assertMathCanonicalPath(this.options.runRoot);
    fs.mkdirSync(this.options.runRoot, { recursive: true, mode: 0o700 });
    this.assertRoot();
    const directories = [
      this.artifactRoot,
      this.objects,
      this.intents,
      this.completed,
      path.join(this.options.runRoot, 'drafts'),
      path.join(this.options.runRoot, 'diagnostics'),
    ];
    // An existing store may have cached readers in other MCP processes. Only
    // creation needs an exclusive lifecycle lease; opening it is read-only.
    const initialized = await withMathRuntimeLease(this.lock('artifact-lifecycle.lock', true), async (lease) => {
      if (this.ledger()) throw new MathArtifactError('conflict');
      for (const directory of directories) {
        assertMathCanonicalPath(directory);
        if (!fs.existsSync(directory)) return false;
        const stat = fs.statSync(directory);
        if (!stat.isDirectory() || (stat.mode & 0o777) !== 0o700) throw new MathArtifactError('integrity');
      }
      assertMathCanonicalPath(this.manifestFile);
      if (!fs.existsSync(this.manifestFile)) return false;
      this.manifest();
      lease.assertHeld();
      return true;
    });
    if (initialized) return;
    await withMathRuntimeLease(this.lock('artifact-lifecycle.lock'), async (lease) => {
      if (this.ledger()) throw new MathArtifactError('conflict');
      for (const directory of directories) {
        assertMathCanonicalPath(directory);
        fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
        if ((fs.statSync(directory).mode & 0o777) !== 0o700) throw new MathArtifactError('integrity');
      }
      lease.assertHeld();
      if (!fs.existsSync(this.manifestFile))
        writeMathJsonDurable(this.manifestFile, {
          schema: 'deepscientist.math.artifacts.v1',
          runId: this.options.runId,
          revision: 0,
          entries: {},
          grants: {},
        });
      this.manifest();
    });
  }

  private verifyObject(
    file: string,
    entry: MathArtifactManifestEntry,
    allowPublicationLink = false,
    validateText = false
  ): { fd: number; stat: fs.BigIntStats } {
    let fd: number;
    try {
      assertMathCanonicalPath(file);
      fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
    } catch {
      throw new MathArtifactError('integrity');
    }
    try {
      const stat = fs.fstatSync(fd, { bigint: true });
      if (
        !stat.isFile() ||
        stat.size !== BigInt(entry.bytes) ||
        (stat.mode & BigInt(0o777)) !== BigInt(0o600) ||
        (stat.nlink !== BigInt(1) && !(allowPublicationLink && stat.nlink === BigInt(2)))
      )
        throw new MathArtifactError('integrity');
      this.options.onHash?.();
      const hash = crypto.createHash('sha256');
      const buffer = Buffer.alloc(65536);
      const decoder = validateText ? new TextDecoder('utf-8', { fatal: true }) : undefined;
      let offset = 0;
      while (offset < entry.bytes) {
        const read = fs.readSync(fd, buffer, 0, Math.min(buffer.length, entry.bytes - offset), offset);
        if (!read) throw new MathArtifactError('integrity');
        hash.update(buffer.subarray(0, read));
        offset += read;
        try {
          decoder?.decode(buffer.subarray(0, read), { stream: true });
        } catch {
          throw new MathArtifactError('invalid');
        }
      }
      try {
        decoder?.decode();
      } catch {
        throw new MathArtifactError('invalid');
      }
      const after = fs.fstatSync(fd, { bigint: true });
      const named = fs.lstatSync(file, { bigint: true });
      if (
        hash.digest('hex') !== entry.sha256 ||
        named.dev !== stat.dev ||
        named.ino !== stat.ino ||
        named.mode !== stat.mode ||
        after.size !== stat.size ||
        after.mtimeNs !== stat.mtimeNs ||
        after.ctimeNs !== stat.ctimeNs
      )
        throw new MathArtifactError('integrity');
      return { fd, stat };
    } catch (error) {
      fs.closeSync(fd);
      throw error;
    }
  }

  private applyIntent(file: string, intent: Intent, manifest: Manifest): void {
    const object = path.join(this.objects, intent.entry.sha256);
    const temporary = path.join(this.objects, intent.tempName);
    const existing = manifest.entries[intent.entry.artifactId];
    if (intent.entry.runId !== this.options.runId) throw new MathArtifactError('integrity');
    if (
      existing &&
      (canonicalMathJson(existing) !== canonicalMathJson(intent.entry) ||
        canonicalMathJson(manifest.grants[existing.artifactId] ?? []) !== canonicalMathJson(intent.grants))
    )
      throw new MathArtifactError('integrity');
    if (!existing && (intent.state === 'manifest_committed' || manifest.revision !== intent.expectedManifestRevision))
      throw new MathArtifactError('integrity');
    const hasTemp = fs.existsSync(temporary);
    const hasObject = fs.existsSync(object);
    if (hasTemp) fs.closeSync(this.verifyObject(temporary, intent.entry, true).fd);
    if (hasObject) fs.closeSync(this.verifyObject(object, intent.entry, hasTemp).fd);
    if (!hasObject) {
      if (existing || !hasTemp) throw new MathArtifactError('integrity');
      fs.linkSync(temporary, object);
      syncMathDirectory(this.objects);
      this.options.fault?.('object_published');
    }
    if (!existing) {
      writeMathJsonDurable(file, { ...intent, state: 'object_published' });
      const next: Manifest = {
        ...manifest,
        revision: manifest.revision + 1,
        entries: { ...manifest.entries, [intent.entry.artifactId]: intent.entry },
        grants: { ...manifest.grants, [intent.entry.artifactId]: intent.grants },
      };
      writeMathJsonDurable(this.manifestFile, next);
      this.options.fault?.('manifest_published');
    }
    writeMathJsonDurable(file, { ...intent, state: 'manifest_committed' });
    this.options.fault?.('manifest_committed');
    // A failed replacement can leave an unpublished staging file. Once the
    // canonical intent is durably committed, only its verified object and
    // manifest are authoritative; obsolete staging bytes may even be torn.
    this.cleanupCommittedStaging(new Set([intent.entry.artifactId]));
    if (hasTemp) {
      fs.unlinkSync(temporary);
      syncMathDirectory(this.objects);
    }
    const completedFile = path.join(this.completed, path.basename(file));
    if (fs.existsSync(completedFile)) throw new MathArtifactError('integrity');
    fs.renameSync(file, completedFile);
    syncMathDirectory(this.completed);
    syncMathDirectory(this.intents);
  }

  // Call only after validating the authoritative intent, manifest and object.
  private cleanupCommittedStaging(artifactIds: ReadonlySet<string>): void {
    let removedStaging = false;
    for (const name of fs.readdirSync(this.intents)) {
      const match =
        /^([A-Za-z0-9_-]{1,128})\.json\.[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}\.tmp$/u.exec(name);
      if (!match || !artifactIds.has(match[1])) continue;
      const stagingFile = path.join(this.intents, name);
      assertMathCanonicalPath(stagingFile);
      const stat = fs.lstatSync(stagingFile);
      if (!stat.isFile() || stat.nlink !== 1 || (stat.mode & 0o777) !== 0o600) throw new MathArtifactError('integrity');
      fs.unlinkSync(stagingFile);
      removedStaging = true;
    }
    if (removedStaging) syncMathDirectory(this.intents);
  }

  private recoverLocked(): void {
    for (const name of fs
      .readdirSync(this.intents)
      .filter((entryName) => entryName.endsWith('.json'))
      .toSorted()) {
      const file = path.join(this.intents, name);
      const parsed = intentSchema.safeParse(readMathJson(file));
      if (!parsed.success || name !== `${parsed.data.entry.artifactId}.json`) throw new MathArtifactError('integrity');
      const intent = parsed.data as Intent;
      this.applyIntent(file, intent, this.manifest());
    }
  }

  private verifyCommittedStore(): void {
    const manifest = this.manifest();
    const verified = new Set<string>();
    const names = fs.readdirSync(this.completed).toSorted();
    if (names.length !== Object.keys(manifest.entries).length) throw new MathArtifactError('integrity');
    for (const name of names) {
      const parsed = intentSchema.safeParse(readMathJson(path.join(this.completed, name)));
      if (!parsed.success) throw new MathArtifactError('integrity');
      const intent = parsed.data as Intent;
      if (
        intent.state !== 'manifest_committed' ||
        name !== `${intent.entry.artifactId}.json` ||
        canonicalMathJson(manifest.entries[intent.entry.artifactId] ?? null) !== canonicalMathJson(intent.entry) ||
        canonicalMathJson(manifest.grants[intent.entry.artifactId] ?? []) !== canonicalMathJson(intent.grants) ||
        fs.existsSync(path.join(this.objects, intent.tempName))
      )
        throw new MathArtifactError('integrity');
      if (!verified.has(intent.entry.sha256)) {
        fs.closeSync(this.verifyObject(path.join(this.objects, intent.entry.sha256), intent.entry).fd);
        verified.add(intent.entry.sha256);
      }
    }
  }

  async recover(): Promise<void> {
    this.assertRoot();
    await withMathRuntimeLease(this.lock('artifact-lifecycle.lock', true), async () => {
      if (this.ledger()) throw new MathArtifactError('conflict');
      await withMathRuntimeLease(this.lock('artifact-writer.lock'), async () => {
        this.recoverLocked();
        this.verifyCommittedStore();
      });
    });
  }

  async publishFile(input: PublishInput & Readonly<{ sourceFile: string }>): Promise<MathArtifactManifestEntry> {
    assertMathCanonicalPath(input.sourceFile);
    const source = fs.openSync(
      input.sourceFile,
      fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK
    );
    try {
      const before = fs.fstatSync(source, { bigint: true });
      if (!before.isFile() || before.nlink !== BigInt(1) || before.size > BigInt(Number.MAX_SAFE_INTEGER))
        throw new MathArtifactError('invalid');
      return await this.publish(input, (target, hash) => {
        const buffer = Buffer.alloc(65536);
        let offset = 0;
        while (offset < Number(before.size)) {
          const read = fs.readSync(source, buffer, 0, Math.min(buffer.length, Number(before.size) - offset), offset);
          if (!read) throw new MathArtifactError('integrity');
          fs.writeFileSync(target, buffer.subarray(0, read));
          hash.update(buffer.subarray(0, read));
          offset += read;
        }
        const after = fs.fstatSync(source, { bigint: true });
        const current = fs.lstatSync(input.sourceFile, { bigint: true });
        if (
          after.size !== before.size ||
          after.mtimeNs !== before.mtimeNs ||
          after.ctimeNs !== before.ctimeNs ||
          current.dev !== before.dev ||
          current.ino !== before.ino
        )
          throw new MathArtifactError('integrity');
        return offset;
      });
    } finally {
      fs.closeSync(source);
    }
  }

  async publishText(input: PublishInput & Readonly<{ text: string }>): Promise<MathArtifactManifestEntry> {
    return this.publish(input, (fd, hash) => {
      const content = Buffer.from(input.text, 'utf8');
      fs.writeFileSync(fd, content);
      hash.update(content);
      return content.length;
    });
  }

  private async publish(
    input: PublishInput,
    copy: (fd: number, hash: crypto.Hash) => number
  ): Promise<MathArtifactManifestEntry> {
    this.assertRoot();
    id.parse(input.artifactId);
    return withMathRuntimeLease(this.lock('artifact-lifecycle.lock', true), async () => {
      if (this.ledger()) throw new MathArtifactError('conflict');
      return withMathRuntimeLease(this.lock('artifact-writer.lock'), async (lease) => {
        this.recoverLocked();
        const manifest = this.manifest();
        const grants = [...new Set(input.grants ?? [])].toSorted();
        if (
          grants.some((grant) => !manifest.entries[grant] || manifest.entries[grant].sensitivity !== 'solver-visible')
        )
          throw new MathArtifactError('unauthorized');
        const tempName = `.${crypto.randomUUID()}.tmp`;
        assertMathCanonicalPath(this.objects);
        const temporary = path.join(this.objects, tempName);
        const intentFile = path.join(this.intents, `${input.artifactId}.json`);
        let intentWritten = false;
        try {
          const fd = fs.openSync(temporary, 'wx', 0o600);
          const hash = crypto.createHash('sha256');
          let size: number;
          try {
            size = copy(fd, hash);
            fs.fsyncSync(fd);
          } finally {
            fs.closeSync(fd);
          }
          syncMathDirectory(this.objects);
          const entry = entrySchema.parse({
            artifactId: input.artifactId,
            runId: this.options.runId,
            assignmentId: input.assignmentId,
            kind: input.kind,
            sensitivity: input.sensitivity,
            mediaType: input.mediaType,
            sha256: hash.digest('hex'),
            bytes: size,
            createdAt: manifest.entries[input.artifactId]?.createdAt ?? new Date(this.now()).toISOString(),
            truncated: false,
          }) as MathArtifactManifestEntry;
          lease.assertHeld();
          if (manifest.entries[input.artifactId]) {
            if (
              canonicalMathJson(manifest.entries[input.artifactId]) !== canonicalMathJson(entry) ||
              canonicalMathJson(manifest.grants[input.artifactId] ?? []) !== canonicalMathJson(grants)
            )
              throw new MathArtifactError('conflict');
            fs.closeSync(this.verifyObject(path.join(this.objects, entry.sha256), entry).fd);
            fs.unlinkSync(temporary);
            syncMathDirectory(this.objects);
            return entry;
          }
          const intent: Intent = {
            schema: 'deepscientist.math.artifact-intent.v1',
            state: 'prepared',
            expectedManifestRevision: manifest.revision,
            tempName,
            entry,
            grants,
          };
          writeMathJsonDurable(intentFile, intent);
          intentWritten = true;
          this.options.fault?.('prepared');
          lease.assertHeld();
          this.applyIntent(intentFile, intent, manifest);
          return entry;
        } catch (error) {
          // rename may have published the intent even if the following directory
          // sync failed. Only a confirmed absent intent permits object cleanup;
          // an uncertain lookup must preserve the bytes for recovery as well.
          if (!intentWritten) {
            try {
              fs.lstatSync(intentFile);
              intentWritten = true;
            } catch (inspectionError) {
              intentWritten = (inspectionError as NodeJS.ErrnoException).code !== 'ENOENT';
            }
          }
          if (!intentWritten) {
            try {
              for (const name of fs
                .readdirSync(this.intents)
                .filter(
                  (candidate) => candidate.startsWith(`${input.artifactId}.json.`) && candidate.endsWith('.tmp')
                )) {
                fs.unlinkSync(path.join(this.intents, name));
              }
              syncMathDirectory(this.intents);
              fs.unlinkSync(temporary);
              syncMathDirectory(this.objects);
            } catch (cleanupError) {
              if ((cleanupError as NodeJS.ErrnoException).code !== 'ENOENT') {
                const failure = new AggregateError(
                  [error, cleanupError],
                  error instanceof Error ? error.message : 'math_artifact_publication_failed',
                  { cause: error }
                );
                throw failure;
              }
            }
          }
          throw error;
        }
      });
    });
  }

  // Metadata is a discovery hint only; selected bodies still pass through read().
  async listMetadata(access: MathArtifactAccess): Promise<readonly MathArtifactManifestEntry[]> {
    this.assertRoot();
    return withMathRuntimeLease(this.lock('artifact-lifecycle.lock', true), async (lease) => {
      const ledger = this.ledger();
      if (ledger && ['deleting', 'deleted'].includes(ledger.state)) throw new MathArtifactError('not_found');
      const entries = Object.values(this.manifest().entries)
        .filter(
          (entry) =>
            entry.sensitivity === 'solver-visible' &&
            (access.role === 'lead' ||
              Boolean(
                access.assignmentId &&
                (entry.assignmentId === access.assignmentId || access.grants?.has(entry.artifactId))
              ))
        )
        .map((entry) => ({ ...entry }));
      lease.assertHeld();
      return entries;
    });
  }

  async grantedClosure(artifactId: string, access: MathArtifactAccess): Promise<readonly string[]> {
    this.assertRoot();
    return withMathRuntimeLease(this.lock('artifact-lifecycle.lock', true), async (lease) => {
      const ledger = this.ledger();
      if (ledger && ['deleting', 'deleted'].includes(ledger.state)) throw new MathArtifactError('not_found');
      const manifest = this.manifest();
      const result = new Set<string>();
      const visit = (current: string): void => {
        if (result.has(current)) return;
        this.authorize(manifest.entries[current], access);
        result.add(current);
        for (const linked of manifest.grants[current] ?? []) visit(linked);
      };
      visit(artifactId);
      lease.assertHeld();
      return [...result].toSorted();
    });
  }

  private authorize(
    entry: MathArtifactManifestEntry | undefined,
    access: MathArtifactAccess
  ): asserts entry is MathArtifactManifestEntry {
    if (!entry) throw new MathArtifactError('not_found');
    if (
      entry.sensitivity !== 'solver-visible' ||
      (access.role === 'worker' &&
        (!access.assignmentId || (entry.assignmentId !== access.assignmentId && !access.grants?.has(entry.artifactId))))
    )
      throw new MathArtifactError('unauthorized');
  }

  private async reader(entry: MathArtifactManifestEntry): Promise<Reader> {
    const pending = this.openingReaders.get(entry.sha256);
    if (pending) return pending;
    const opening = this.openReader(entry);
    this.openingReaders.set(entry.sha256, opening);
    try {
      return await opening;
    } finally {
      this.openingReaders.delete(entry.sha256);
    }
  }

  private async openReader(entry: MathArtifactManifestEntry): Promise<Reader> {
    const object = path.join(this.objects, entry.sha256);
    const cached = this.readers.get(entry.sha256);
    if (cached) {
      try {
        cached.lease.assertHeld();
        const stat = fs.lstatSync(object, { bigint: true });
        if (
          stat.ino === cached.stat.ino &&
          stat.dev === cached.stat.dev &&
          stat.size === cached.stat.size &&
          stat.mtimeNs === cached.stat.mtimeNs &&
          stat.ctimeNs === cached.stat.ctimeNs
        ) {
          this.readers.delete(entry.sha256);
          this.readers.set(entry.sha256, cached);
          return cached;
        }
      } catch {
        /* A stale handle must release its lifecycle lease before reopening. */
      }
      await this.closeReader(entry.sha256);
    }
    if (this.readers.size >= MAX_CACHED_READERS) {
      const oldest = this.readers.keys().next().value;
      if (oldest) await this.closeReader(oldest);
    }
    let releaseHold!: () => void;
    const hold = new Promise<void>((resolve) => {
      releaseHold = resolve;
    });
    let accept!: (reader: Reader) => void;
    let reject!: (error: unknown) => void;
    const ready = new Promise<Reader>((resolve, fail) => {
      accept = resolve;
      reject = fail;
    });
    const task = withMathRuntimeLease(this.lock('artifact-lifecycle.lock', true), async (lease) => {
      const ledger = this.ledger();
      if (ledger && ['deleting', 'deleted'].includes(ledger.state)) throw new MathArtifactError('not_found');
      const opened = this.verifyObject(object, entry, false, true);
      const reader: Reader = {
        ...opened,
        lease,
        release: async () => {
          releaseHold();
          await task;
        },
      };
      lease.signal.addEventListener('abort', releaseHold, { once: true });
      this.readers.set(entry.sha256, reader);
      accept(reader);
      try {
        await hold;
      } finally {
        lease.signal.removeEventListener('abort', releaseHold);
        if (this.readers.get(entry.sha256) === reader) this.readers.delete(entry.sha256);
        if (reader.timer) clearTimeout(reader.timer);
        fs.closeSync(opened.fd);
      }
    });
    void task.catch(reject);
    return ready;
  }

  private async closeReader(objectDigest: string): Promise<void> {
    const reader = this.readers.get(objectDigest);
    if (!reader) return;
    this.readers.delete(objectDigest);
    if (reader.timer) clearTimeout(reader.timer);
    await reader.release();
  }

  private serializeRead<T>(operation: () => Promise<T>): Promise<T> {
    const result = this.readerQueue.then(operation, operation);
    this.readerQueue = result.then(
      (): void => undefined,
      (): void => undefined
    );
    return result;
  }

  closeReaders(): Promise<void> {
    return this.serializeRead(() => this.closeReadersLocked());
  }

  private async closeReadersLocked(): Promise<void> {
    await Promise.allSettled(this.openingReaders.values());
    const errors = await Promise.allSettled(
      [...this.readers.keys()].map((objectDigest) => this.closeReader(objectDigest))
    );
    const failed = errors.find((result) => result.status === 'rejected');
    if (failed?.status === 'rejected') throw failed.reason;
  }

  read(request: MathArtifactReadRequest, access: MathArtifactAccess): Promise<MathArtifactReadResponse> {
    // A short serialized read prevents eviction from closing another caller's acquired handle.
    return this.serializeRead(() => this.readLocked(request, access));
  }

  private async readLocked(
    request: MathArtifactReadRequest,
    access: MathArtifactAccess
  ): Promise<MathArtifactReadResponse> {
    this.assertRoot();
    const input = normalizeMathArtifactRead(request);
    const ref = parseMathArtifactReference(input.ref);
    if (ref?.scheme !== 'math-artifact') throw new MathArtifactError('invalid');
    if (ref.runId !== this.options.runId) throw new MathArtifactError('unauthorized');
    const ledger = this.ledger();
    if (ledger && ['deleting', 'deleted'].includes(ledger.state)) throw new MathArtifactError('not_found');
    const entry = this.manifest().entries[ref.artifactId];
    this.authorize(entry, access);
    const reader = await this.reader(entry);
    reader.lease.assertHeld();
    if (reader.timer) clearTimeout(reader.timer);
    reader.timer = setTimeout(() => {
      void this.closeReader(entry.sha256).catch(() => {});
    }, 30_000);
    reader.timer.unref();
    const offset = input.offsetBytes ?? 0;
    if (offset > entry.bytes) throw new MathArtifactError('invalid');
    const buffer = Buffer.alloc(Math.min(input.maxBytes ?? 2048, entry.bytes - offset));
    const read = fs.readSync(reader.fd, buffer, 0, buffer.length, offset);
    if (read !== buffer.length || (read && (buffer[0] & 0xc0) === 0x80)) throw new MathArtifactError('invalid');
    const decoder = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true });
    for (let length = read; length >= 0; length--) {
      if (!length && offset < entry.bytes) throw new MathArtifactError('invalid');
      let text: string;
      try {
        text = decoder.decode(buffer.subarray(0, length));
      } catch {
        continue;
      }
      const result = {
        text,
        sha256: entry.sha256,
        totalBytes: entry.bytes,
        ...(offset + length < entry.bytes ? { nextOffsetBytes: offset + length } : {}),
      };
      if (Buffer.byteLength(JSON.stringify(result), 'utf8') < 4096) {
        reader.lease.assertHeld();
        return result;
      }
    }
    throw new MathArtifactError('invalid');
  }

  async markTerminal(retainMs = 7 * 24 * 60 * 60 * 1000): Promise<void> {
    this.assertRoot();
    await withMathRuntimeLease(this.lock('artifact-lifecycle.lock'), async () => {
      if (this.ledger()) return;
      const now = this.now();
      if (!Number.isSafeInteger(retainMs) || retainMs < 0) throw new MathArtifactError('invalid');
      this.recoverLocked();
      this.verifyCommittedStore();
      writeMathJsonDurable(this.ledgerFile, {
        schema: 'deepscientist.math.artifact-gc.v1',
        runId: this.options.runId,
        terminalAt: now,
        retainUntil: now + retainMs,
        pin: false,
        state: 'retained',
        manifestDigest: mathDigest(canonicalMathJson(this.manifest())),
      });
    });
  }

  async pin(value: boolean): Promise<void> {
    this.assertRoot();
    await withMathRuntimeLease(this.lock('artifact-lifecycle.lock'), async () => {
      const ledger = this.ledger();
      if (!ledger || ['deleting', 'deleted'].includes(ledger.state)) throw new MathArtifactError('conflict');
      writeMathJsonDurable(this.ledgerFile, { ...ledger, pin: value });
    });
  }

  async collectGarbage(): Promise<boolean> {
    this.assertRoot();
    return withMathRuntimeLease(this.lock('artifact-lifecycle.lock'), async (lease) => {
      const ledger = this.ledger();
      if (!ledger || ledger.pin || ledger.retainUntil > this.now()) return false;
      if (ledger.state === 'deleted') return true;
      if (ledger.state !== 'deleting') {
        this.verifyCommittedStore();
        const manifest = this.manifest();
        if (ledger.manifestDigest !== mathDigest(canonicalMathJson(manifest))) throw new MathArtifactError('integrity');
        // Older recovery could finish publication while leaving failed replacements.
        // Validate the retained snapshot before discarding those obsolete bytes.
        this.cleanupCommittedStaging(new Set(Object.keys(manifest.entries)));
        if (fs.readdirSync(this.intents).some((name) => name !== 'completed')) throw new MathArtifactError('integrity');
        writeMathJsonDurable(this.ledgerFile, { ...ledger, state: 'eligible' });
        writeMathJsonDurable(this.ledgerFile, { ...ledger, state: 'deleting' });
        this.options.fault?.('gc_deleting');
      }
      for (const name of ['artifacts', 'drafts', 'diagnostics']) {
        const target = path.join(this.options.runRoot, name);
        assertMathCanonicalPath(target);
        lease.assertHeld();
        fs.rmSync(target, { recursive: true, force: true });
        this.options.fault?.(`gc_${name}_deleted`);
      }
      syncMathDirectory(this.options.runRoot);
      writeMathJsonDurable(this.ledgerFile, { ...ledger, state: 'deleted' });
      return true;
    });
  }
}
