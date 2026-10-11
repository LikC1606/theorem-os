import fs from 'node:fs';
import path from 'node:path';

export const isMathPathWithin = (root: string, target: string): boolean => {
  const relative = path.relative(root, target);
  return relative === '' || (!path.isAbsolute(relative) && relative !== '..' && !relative.startsWith(`..${path.sep}`));
};

export function assertMathCanonicalPath(target: string): void {
  if (!path.isAbsolute(target) || path.resolve(target) !== target) throw new Error('math_path_invalid');
  let current = target;
  while (!fs.existsSync(current)) {
    try {
      if (fs.lstatSync(current).isSymbolicLink()) throw new Error('math_path_invalid');
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
    }
    const parent = path.dirname(current);
    if (parent === current) throw new Error('math_path_invalid');
    current = parent;
  }
  if (fs.realpathSync(current) !== current) throw new Error('math_path_invalid');
}
