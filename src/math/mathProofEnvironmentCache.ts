import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathJson } from "./mathRuntimeIo";
import { assertMathCanonicalPath } from "./paths";

const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const entrySchema = z.object({
  schema: z.literal('deepscientist.math.proof-environment-cache.v1'),
  fingerprint: digest,
  imageName: z.string().regex(/^[a-f0-9-]+\.squashfs$/u),
  imageSha256: digest,
  imageBytes: z.number().int().positive(),
  metadataHash: digest,
  stats: z.object({
    files: z.number().int().nonnegative(),
    bytes: z.number().int().nonnegative(),
    publications: z.literal(1),
  }),
});
export type MathProofEnvironmentCacheEntry = z.infer<typeof entrySchema>;

function readPrivateFile(file: string, maxBytes: number): Buffer {
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const stat = fs.fstatSync(fd);
    if (
      !stat.isFile() ||
      stat.nlink !== 1 ||
      (stat.mode & 0o077) !== 0 ||
      (process.getuid && stat.uid !== process.getuid()) ||
      stat.size > maxBytes
    )
      throw new Error('Invalid private proof environment cache file.');
    return fs.readFileSync(fd);
  } finally {
    fs.closeSync(fd);
  }
}

/** Host-private disk cache. Each run still receives its own unlinked image and mount. */
export function openMathProofEnvironmentCache(root: string) {
  assertMathCanonicalPath(root);
  fs.mkdirSync(root, { recursive: true, mode: 0o700 });
  const stat = fs.lstatSync(root);
  const filesystem = fs.statfsSync(root);
  if (
    !stat.isDirectory() ||
    (stat.mode & 0o777) !== 0o700 ||
    (process.getuid && stat.uid !== process.getuid()) ||
    [0x01021994, 0x858458f6].includes(Number(filesystem.type))
  )
    throw new Error('Proof environment cache requires a private disk directory.');
  const keyPath = path.join(root, 'key');
  try {
    fs.writeFileSync(keyPath, crypto.randomBytes(32), { flag: 'wx', mode: 0o600 });
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
  }
  const key = readPrivateFile(keyPath, 32);
  if (key.length !== 32) throw new Error('Invalid proof environment cache key.');
  const signature = (entry: MathProofEnvironmentCacheEntry) =>
    crypto
      .createHmac('sha256', key)
      .update('deepscientist.math.proof-environment-cache.v1\0')
      .update(canonicalMathJson(entry))
      .digest('hex');
  return {
    read(fingerprint: string): MathProofEnvironmentCacheEntry | undefined {
      try {
        digest.parse(fingerprint);
        const value = JSON.parse(readPrivateFile(path.join(root, `${fingerprint}.json`), 4096).toString());
        const entry = entrySchema.parse(value.entry);
        const actual = Buffer.from(digest.parse(value.signature), 'hex');
        if (entry.fingerprint !== fingerprint || !crypto.timingSafeEqual(actual, Buffer.from(signature(entry), 'hex')))
          return undefined;
        const image = fs.lstatSync(path.join(root, entry.imageName));
        if (
          !image.isFile() ||
          image.nlink !== 1 ||
          image.size !== entry.imageBytes ||
          (image.mode & 0o777) !== 0o400 ||
          (process.getuid && image.uid !== process.getuid())
        )
          return undefined;
        return entry;
      } catch {
        return undefined;
      }
    },
    imagePath(entry: MathProofEnvironmentCacheEntry) {
      return path.join(root, entrySchema.parse(entry).imageName);
    },
    createImagePath(fingerprint: string) {
      return path.join(root, `${digest.parse(fingerprint)}-${crypto.randomUUID()}.squashfs`);
    },
    invalidate(fingerprint: string) {
      fs.rmSync(path.join(root, `${digest.parse(fingerprint)}.json`), { force: true });
    },
    publish(entry: MathProofEnvironmentCacheEntry) {
      entry = entrySchema.parse(entry);
      const temporary = path.join(root, `${crypto.randomUUID()}.tmp`);
      try {
        const fd = fs.openSync(temporary, 'wx', 0o600);
        try {
          fs.writeFileSync(fd, `${canonicalMathJson({ entry, signature: signature(entry) })}\n`);
          fs.fsyncSync(fd);
        } finally {
          fs.closeSync(fd);
        }
        fs.renameSync(temporary, path.join(root, `${entry.fingerprint}.json`));
      } finally {
        fs.rmSync(temporary, { force: true });
      }
    },
  };
}
