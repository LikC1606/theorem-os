import { createServer, request as httpRequest, type IncomingHttpHeaders } from 'node:http';
import { request as httpsRequest } from 'node:https';
import fs from 'node:fs';
import { createInterface } from 'node:readline';
import { basename, dirname, join } from 'node:path';
import { randomUUID, timingSafeEqual } from 'node:crypto';
import { syncMathDirectory, withMathRuntimeLease, type MathLease } from "./mathRuntimeIo";

type Waiting = { group: string; start: () => void; cancelled: boolean };

type MathRequestGatewayOptions = {
  upstreamBaseUrl: string;
  secret: string;
  concurrency: number;
  eventsFile: string;
  port?: number;
  transportConnectTimeoutMs?: number;
  tcpKeepAliveInitialDelayMs?: number;
};

export async function startMathRequestGateway(options: MathRequestGatewayOptions) {
  const upstream = new URL(options.upstreamBaseUrl);
  if (!['http:', 'https:'].includes(upstream.protocol) || upstream.username || upstream.password)
    throw new Error('Invalid upstream URL');
  if (!options.secret || !Number.isSafeInteger(options.concurrency) || options.concurrency < 1)
    throw new Error('Invalid gateway configuration');
  const connectTimeout = options.transportConnectTimeoutMs ?? 30_000;
  const keepAliveDelay = options.tcpKeepAliveInitialDelayMs ?? 30_000;
  if (![connectTimeout, keepAliveDelay].every((value) => Number.isSafeInteger(value) && value > 0))
    throw new Error('Invalid gateway transport health configuration');
  fs.mkdirSync(dirname(options.eventsFile), { recursive: true });
  // A port does not identify a journal: ephemeral/different ports may share the same file.
  // Canonicalize its directory so alternate parent paths also share the OS-owned lease.
  const eventsFile = join(fs.realpathSync(dirname(options.eventsFile)), basename(options.eventsFile));
  return new Promise<Awaited<ReturnType<typeof startOwnedMathRequestGateway>>>((resolve, reject) => {
    let release!: () => void;
    const released = new Promise<void>((done) => {
      release = done;
    });
    const lifetime = withMathRuntimeLease(
      { lockPath: `${eventsFile}.lock`, flockExecutable: '/usr/bin/flock' },
      async (lease) => {
        const gateway = await startOwnedMathRequestGateway({ ...options, eventsFile }, lease);
        let closePromise: Promise<void> | undefined;
        resolve({
          ...gateway,
          close: () =>
            (closePromise ??= (async () => {
              try {
                await gateway.close();
              } finally {
                release();
                await lifetime;
              }
            })()),
        });
        await released;
      }
    );
    void lifetime.catch(reject);
  });
}

async function startOwnedMathRequestGateway(options: MathRequestGatewayOptions, lease: MathLease) {
  const upstream = new URL(options.upstreamBaseUrl);
  const connectTimeout = options.transportConnectTimeoutMs ?? 30_000;
  const keepAliveDelay = options.tcpKeepAliveInitialDelayMs ?? 30_000;
  try {
    const stat = fs.lstatSync(options.eventsFile);
    if (
      stat.isSymbolicLink() ||
      !stat.isFile() ||
      stat.nlink !== 1 ||
      (process.getuid !== undefined && stat.uid !== process.getuid())
    )
      throw new Error('math_gateway_event_store_invalid');
    if ((stat.mode & 0o077) !== 0) fs.chmodSync(options.eventsFile, 0o600);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
  }
  let storageBroken = false;
  const writeFully = (fd: number, value: string | Uint8Array): void => {
    const bytes = typeof value === 'string' ? Buffer.from(value, 'utf8') : Buffer.from(value);
    let offset = 0;
    while (offset < bytes.length) {
      const written = fs.writeSync(fd, bytes, offset, bytes.length - offset, null);
      if (!Number.isSafeInteger(written) || written <= 0) throw new Error('math_gateway_event_store_short_write');
      offset += written;
    }
  };
  const appendDurable = (value: string): void => {
    lease.assertHeld();
    if (storageBroken) throw new Error('math_gateway_event_store_unavailable');
    const staged = value.trim().length > 0;
    const pendingFile = staged ? `${options.eventsFile}.pending.${randomUUID()}` : undefined;
    let fd: number | undefined;
    let pendingFd: number | undefined;
    try {
      if (pendingFile) {
        pendingFd = fs.openSync(
          pendingFile,
          fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_NOFOLLOW,
          0o600
        );
        fs.writeFileSync(pendingFd, value, 'utf8');
        fs.fsyncSync(pendingFd);
        syncMathDirectory(dirname(options.eventsFile));
      }
      fd = fs.openSync(
        options.eventsFile,
        fs.constants.O_WRONLY | fs.constants.O_APPEND | fs.constants.O_CREAT | fs.constants.O_NOFOLLOW,
        0o600
      );
      const stat = fs.fstatSync(fd);
      if (
        !stat.isFile() ||
        stat.nlink !== 1 ||
        (process.getuid !== undefined && stat.uid !== process.getuid()) ||
        (stat.mode & 0o777) !== 0o600
      )
        throw new Error('math_gateway_event_store_invalid');
      writeFully(fd, value);
      fs.fsyncSync(fd);
      if (pendingFile) {
        fs.unlinkSync(pendingFile);
        syncMathDirectory(dirname(options.eventsFile));
      }
    } catch (error) {
      storageBroken = true;
      throw error;
    } finally {
      if (pendingFd !== undefined) fs.closeSync(pendingFd);
      if (fd !== undefined) fs.closeSync(fd);
    }
  };
  // Materialize the journal before the server can enter startup recovery.
  appendDurable('');
  const queues = new Map<string, Waiting[]>();
  const turns: string[] = [];
  let active = 0;
  let lastGroup: string | undefined;
  let closed = false;
  let telemetryFailed = false;
  let ready = false;
  const instanceId = randomUUID();
  const aborts = new Set<() => void>();
  const capability = { enabled: true, concurrency: options.concurrency, scope: 'math_run_root', protocolVersion: 1 };
  const record = (event: Record<string, unknown>): boolean => {
    try {
      appendDurable(`${JSON.stringify({ eventId: randomUUID(), instanceId, ...event })}\n`);
      return true;
    } catch {
      telemetryFailed = true;
      queueMicrotask(() => {
        for (const abort of aborts) abort();
      });
      return false;
    }
  };
  const drain = () => {
    while (!closed && !telemetryFailed && active < options.concurrency && turns.length) {
      if (turns.length > 1 && turns[0] === lastGroup) turns.push(turns.shift()!);
      const group = turns.shift()!;
      const queue = queues.get(group)!;
      const next = queue.shift()!;
      if (queue.length) turns.push(group);
      else queues.delete(group);
      if (next.cancelled) continue;
      lastGroup = group;
      active++;
      next.start();
    }
  };
  const server = createServer((req, res) => {
    if (req.url === '/health' && req.method === 'GET') {
      res.statusCode = telemetryFailed || !ready ? 503 : 200;
      res.setHeader('content-type', 'application/json');
      res.end(
        JSON.stringify({
          math_request_gate: { ...capability, enabled: !telemetryFailed && ready },
          ...(!ready ? { error: 'request_recovery_in_progress' } : {}),
          ...(telemetryFailed ? { error: 'request_event_storage_unavailable' } : {}),
          recovery: telemetryFailed ? 'restart_after_storage_recovery' : 'none',
          active,
          queued: [...queues.values()].reduce((n, q) => n + q.length, 0),
        })
      );
      return;
    }
    if (telemetryFailed || closed || !ready) {
      res.writeHead(503).end();
      return;
    }
    const auth = req.headers['x-deepscientist-gate-secret'];
    const group = req.headers['x-deepscientist-run-root'];
    if (
      typeof auth !== 'string' ||
      Buffer.byteLength(auth) !== Buffer.byteLength(options.secret) ||
      !timingSafeEqual(Buffer.from(auth), Buffer.from(options.secret))
    ) {
      res.writeHead(401).end();
      return;
    }
    if (typeof group !== 'string' || !group || group.length > 4096 || !/^[a-zA-Z0-9_%./:-]+$/.test(group)) {
      res.writeHead(400).end('Missing run identity');
      return;
    }
    const requestId = randomUUID();
    req.socket.setKeepAlive(true, keepAliveDelay);
    const queuedAt = new Date().toISOString();
    let admittedAt: string | undefined;
    let firstByteAt: string | undefined;
    let httpStatus: number | undefined;
    let finished = false;
    let abortUpstream: (() => void) | undefined;
    const finish = (outcome: string) => {
      if (finished) return;
      finished = true;
      waiting.cancelled = true;
      aborts.delete(abort);
      const queue = queues.get(group);
      if (queue) {
        const index = queue.indexOf(waiting);
        if (index >= 0) queue.splice(index, 1);
        if (!queue.length) {
          queues.delete(group);
          const turn = turns.indexOf(group);
          if (turn >= 0) turns.splice(turn, 1);
        }
      }
      record({
        requestId,
        runRoot: group,
        queuedAt,
        admittedAt,
        firstByteAt,
        finishedAt: new Date().toISOString(),
        outcome,
        httpStatus,
      });
      if (admittedAt) active--;
      drain();
    };
    const abort = () => {
      abortUpstream?.();
      finish('cancelled');
      res.destroy();
    };
    const waiting: Waiting = {
      group,
      cancelled: false,
      start: () => {
        admittedAt = new Date().toISOString();
        if (!record({ requestId, runRoot: group, queuedAt, admittedAt, outcome: 'admitted' })) {
          finish('telemetry_error');
          res.writeHead(503).end();
          return;
        }
        // Only origin-relative paths are forwarded; clients cannot select an upstream host.
        const target = new URL(upstream);
        const incoming = new URL(req.url ?? '/', 'http://localhost');
        target.pathname = `${upstream.pathname.replace(/\/$/, '')}/${incoming.pathname.replace(/^\//, '')}`;
        target.search = incoming.search;
        const headers: IncomingHttpHeaders = { ...req.headers, host: upstream.host };
        const connectionHeaders = String(headers.connection ?? '')
          .split(',')
          .map((value) => value.trim().toLowerCase());
        for (const name of [
          ...connectionHeaders,
          'connection',
          'proxy-connection',
          'keep-alive',
          'transfer-encoding',
          'upgrade',
          'te',
          'trailer',
          'x-deepscientist-gate-secret',
          'x-deepscientist-run-root',
        ])
          delete headers[name];
        const outgoing = (upstream.protocol === 'https:' ? httpsRequest : httpRequest)(
          target,
          { method: req.method, headers },
          (response) => {
            httpStatus = response.statusCode ?? 502;
            if (httpStatus >= 300 && httpStatus < 400) {
              response.resume();
              finish('upstream_redirect_rejected');
              res.writeHead(502).end('Upstream redirect is not supported by the request gateway');
              return;
            }
            const responseHeaders = { ...response.headers };
            delete responseHeaders.connection;
            delete responseHeaders['transfer-encoding'];
            res.writeHead(httpStatus, responseHeaders);
            response.once('data', () => {
              firstByteAt = new Date().toISOString();
            });
            response.on('error', () => {
              finish('upstream_error');
              res.destroy();
            });
            response.on('aborted', () => {
              finish('upstream_aborted');
              res.destroy();
            });
            response.on('end', () => finish(httpStatus! >= 400 ? 'http_error' : 'completed'));
            response.pipe(res);
          }
        );
        abortUpstream = () => outgoing.destroy();
        // TCP probes detect dead peers without imposing an idle or research deadline.
        outgoing.on('socket', (socket) => {
          socket.setKeepAlive(true, keepAliveDelay);
          if (!socket.connecting) return;
          const connectedEvent = upstream.protocol === 'https:' ? 'secureConnect' : 'connect';
          const timer = setTimeout(
            () => outgoing.destroy(new Error('upstream_transport_connect_failed')),
            connectTimeout
          );
          timer.unref();
          const clear = () => {
            clearTimeout(timer);
            socket.removeListener(connectedEvent, clear);
            socket.removeListener('close', clear);
          };
          socket.once(connectedEvent, clear);
          socket.once('close', clear);
        });
        outgoing.on('error', () => {
          finish('upstream_error');
          if (!res.headersSent) res.writeHead(502).end();
          else res.destroy();
        });
        req.pipe(outgoing);
      },
    };
    aborts.add(abort);
    req.on('aborted', abort);
    req.on('error', abort);
    res.on('close', () => {
      if (!res.writableFinished) abort();
    });
    if (!record({ requestId, runRoot: group, queuedAt, outcome: 'queued' })) {
      finish('telemetry_error');
      res.writeHead(503).end();
      return;
    }
    if (!queues.has(group)) {
      queues.set(group, []);
      turns.push(group);
    }
    queues.get(group)!.push(waiting);
    drain();
  });
  // Research duration is unrestricted. Each stream lives until completion or disconnect.
  server.requestTimeout = 0;
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(options.port ?? 0, '127.0.0.1', resolve);
  });
  const address = server.address();
  if (!address || typeof address === 'string') throw new Error('Gateway failed to bind');
  // Both the journal lease and port are held before startup recovery can retire old requests.
  try {
    const pending = new Map<string, Record<string, unknown>>();
    const recoveredEventIds = new Set<string>();
    const stagedEvents: string[] = [];
    const validStagedEvents: { file: string; event: Record<string, unknown>; replay: boolean }[] = [];
    for (const name of fs.readdirSync(dirname(options.eventsFile))) {
      if (!name.startsWith(`${basename(options.eventsFile)}.pending.`)) continue;
      const file = join(dirname(options.eventsFile), name);
      const stat = fs.lstatSync(file);
      if (stat.isSymbolicLink() || !stat.isFile() || stat.nlink !== 1 || (stat.mode & 0o777) !== 0o600)
        throw new Error('math_gateway_event_store_invalid');
      stagedEvents.push(file);
    }
    // Bound deduplication memory to the sidecars being recovered, not journal history.
    const stagedEventIds = new Set<string>();
    for (const file of stagedEvents) {
      // An unreadable sidecar may hold the only complete terminal event. Fail recovery
      // on I/O errors rather than falsely retiring that request as interrupted.
      const stagedBytes = fs.readFileSync(file, 'utf8');
      try {
        const event = JSON.parse(stagedBytes);
        if (!event || typeof event !== 'object' || Array.isArray(event)) continue;
        if (typeof event.eventId !== 'string' || typeof event.instanceId !== 'string') continue;
        if (typeof event.requestId !== 'string' && event.kind !== 'gateway_started') continue;
        validStagedEvents.push({ file, event, replay: false });
        stagedEventIds.add(event.eventId);
      } catch {
        /* Preserve a staged event for the next restart when its write tore. */
      }
    }
    const input = fs.createReadStream(options.eventsFile);
    const history = createInterface({ input, crlfDelay: Infinity });
    let readError: Error | undefined;
    input.on('error', (error) => {
      readError = error;
      history.close();
    });
    for await (const line of history) {
      try {
        const event = JSON.parse(line);
        if (!event || typeof event !== 'object' || Array.isArray(event)) continue;
        if (typeof event.eventId === 'string' && stagedEventIds.has(event.eventId))
          recoveredEventIds.add(event.eventId);
        if (typeof event.requestId !== 'string') continue;
        const previous = pending.get(event.requestId);
        if (!previous?.finishedAt || event.finishedAt) pending.set(event.requestId, { ...previous, ...event });
      } catch {
        /* Preserve earlier complete events when a crash tore the tail. */
      }
    }
    if (readError) throw readError;
    for (const staged of validStagedEvents) {
      const { event } = staged;
      staged.replay = !recoveredEventIds.has(event.eventId as string);
      recoveredEventIds.add(event.eventId as string);
      if (!staged.replay || typeof event.requestId !== 'string') continue;
      const previous = pending.get(event.requestId);
      if (!previous?.finishedAt || event.finishedAt) pending.set(event.requestId, { ...previous, ...event });
    }
    appendDurable('\n');
    // A prior attempt may have appended an event before sidecar cleanup failed.
    // Replay each event only once, including duplicates left by failed recovery,
    // while keeping every sidecar until its canonical journal copy is durable.
    for (const { event, replay } of validStagedEvents) {
      if (replay) appendDurable(`${JSON.stringify(event)}\n`);
    }
    const recoveredAt = new Date().toISOString();
    for (const event of pending.values()) {
      if (event.finishedAt) continue;
      if (
        !record({
          ...event,
          eventId: randomUUID(),
          instanceId,
          previousInstanceId: event.instanceId ?? null,
          finishedAt: recoveredAt,
          completionTiming: 'recovered_unknown',
          outcome: 'interrupted',
        })
      )
        throw new Error('Request recovery telemetry could not be persisted');
    }
    if (!record({ kind: 'gateway_started', recordedAt: recoveredAt }))
      throw new Error('Gateway startup telemetry could not be persisted');
    for (const { file } of validStagedEvents) {
      try {
        fs.unlinkSync(file);
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
      }
    }
    if (stagedEvents.length) syncMathDirectory(dirname(options.eventsFile));
    ready = true;
  } catch (error) {
    await new Promise<void>((resolve) => server.close(() => resolve()));
    throw error;
  }
  let closePromise: Promise<void> | undefined;
  return {
    url: `http://127.0.0.1:${address.port}`,
    capability,
    close: () =>
      (closePromise ??= (async () => {
        closed = true;
        for (const abort of aborts) abort();
        await new Promise<void>((resolve, reject) => {
          server.close((error) => (error ? reject(error) : resolve()));
          server.closeAllConnections();
        });
      })()),
  };
}
