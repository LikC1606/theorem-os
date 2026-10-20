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

/** Run `work` over `items` with at most `limit` concurrent workers, each taking the next unclaimed item in order. */
export async function forEachWithConcurrency<T>(items: readonly T[], limit: number, work: (item: T) => Promise<void>): Promise<void> {
  let next = 0;
  const worker = async (): Promise<void> => {
    // eslint-disable-next-line no-await-in-loop
    while (next < items.length) await work(items[next++]!);
  };
  await Promise.all(Array.from({ length: Math.min(limit, items.length) }, worker));
}
