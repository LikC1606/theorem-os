import { closeAllMathematicsLeanLspSessions } from "./leanLspSession";
import { closeMathWorkerProofSessions } from "./mathWorkerProofSession";
import { closeAllSharedLeanPackages } from "./leanSharedPackages";

export type MathMcpShutdownState = 'running' | 'stopping' | 'stopped';

let activeGate: { state: MathMcpShutdownState } | undefined;

/** Handlers can reject new writes while the transport drains. */
export function isMathMcpShuttingDown(): boolean {
  return activeGate?.state !== undefined && activeGate.state !== 'running';
}

export function assertMathMcpRunning(): void {
  if (isMathMcpShuttingDown()) throw new Error('math_mcp_shutting_down');
}

/** Stdio EOF and termination must also release persistent sandbox processes. */
export function installMathMcpShutdown(closeServer: () => Promise<void>, stdio = true): void {
  const gate = { state: 'running' as MathMcpShutdownState };
  activeGate = gate;
  const shutdown = async (code: number) => {
    if (gate.state !== 'running') return;
    gate.state = 'stopping';
    const fallback = setTimeout(() => process.exit(code), 5_000);
    fallback.unref();
    try {
      // Drain proof queues before closing their shared Lean transports. Each
      // cleanup remains independent so one failure cannot skip later stages.
      await Promise.allSettled([closeMathWorkerProofSessions()]);
      await Promise.allSettled([closeAllMathematicsLeanLspSessions()]);
      closeAllSharedLeanPackages();
      await Promise.allSettled([closeServer()]);
    } finally {
      gate.state = 'stopped';
      clearTimeout(fallback);
      process.exit(code);
    }
  };
  process.once('SIGTERM', () => {
    void shutdown(143);
  });
  process.once('SIGINT', () => {
    void shutdown(130);
  });
  if (stdio)
    process.stdin.once('end', () => {
      void shutdown(0);
    });
}
