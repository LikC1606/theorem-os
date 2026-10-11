type Waiter = { resolve: () => void; signal?: AbortSignal; onAbort: () => void };

/** Each limiter owns an independent pool; capacity is reserved before waking a waiter. */
export function createMathOperationLimiter(capacity: () => number) {
  let active = 0;
  const waiters = new Set<Waiter>();
  return async <T>(operation: () => Promise<T>, signal?: AbortSignal): Promise<T> => {
    signal?.throwIfAborted();
    if (active < capacity() && waiters.size === 0) active++;
    else await new Promise<void>((resolve, reject) => {
      const waiter: Waiter = { resolve, signal, onAbort: () => {
        waiters.delete(waiter);
        reject(signal!.reason);
      } };
      waiters.add(waiter);
      signal?.addEventListener('abort', waiter.onAbort, { once: true });
    });
    try {
      signal?.throwIfAborted();
      return await operation();
    } finally {
      active--;
      for (const waiter of waiters) {
        if (active >= capacity()) break;
        waiters.delete(waiter);
        waiter.signal?.removeEventListener('abort', waiter.onAbort);
        active++;
        waiter.resolve();
      }
    }
  };
}
