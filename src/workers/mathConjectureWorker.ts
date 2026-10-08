import { parentPort, workerData } from 'node:worker_threads';
import { parseMathSynthesisInput, runMathConjectureSynthesis } from "../math/mathConjectureSynthesis";

// Node MessagePort has no browser targetOrigin parameter.
/* oxlint-disable unicorn/require-post-message-target-origin */

try {
  const input = parseMathSynthesisInput(workerData.input);
  parentPort!.postMessage({ result: runMathConjectureSynthesis(input, { deadlineAt: workerData.deadlineAt }) });
} catch (error) {
  parentPort!.postMessage({ error: error instanceof Error ? error.message : 'math_synthesis_failed' });
}
