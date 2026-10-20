import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

/** Creates a fresh real-path temporary directory; callers remove it in afterEach. */
export function temporaryDirectory(prefix: string): string {
  return fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), prefix)));
}
