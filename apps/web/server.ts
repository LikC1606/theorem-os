import http, { type IncomingMessage, type ServerResponse } from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { z } from 'zod';
import { getWebEnvironments, readWebConfig, webDefaults, webLimits, webTemplates, type WebConfig } from './config';
import { DockerWebRunner, type WebRunner } from './runner';
import { WebJobs } from './jobs';
import type { WebRunInput, WebSession } from './shared';
import { researchModulePlanSchema } from '../../src/solver/modules/policy';

const inputSchema = z.object({
  providerId: z.string().min(1).max(40), apiKey: z.string().min(8).max(4096).regex(/^[\x21-\x7e]+$/),
  model: z.string().trim().min(1).max(128).regex(/^[a-zA-Z0-9][a-zA-Z0-9._:/-]*$/),
  effort: z.enum(['low', 'medium', 'high', 'xhigh']),
  environment: z.enum(['standard', 'mathlib']).default('standard'),
  source: z.string().trim().min(1).refine(value => Buffer.byteLength(value) <= webLimits.maxSourceBytes),
  task: z.string().trim().min(1).refine(value => Buffer.byteLength(value) <= webLimits.maxTaskBytes),
  maxTurns: z.number().int().min(1).max(webLimits.maxTurns),
  maxRunSeconds: z.number().int().min(30).max(webLimits.maxRunSeconds),
  workers: z.number().int().min(1).max(webLimits.maxWorkers),
  coordination: z.enum(['cooperative', 'independent']),
  modulePlan: researchModulePlanSchema.optional(),
}).strict();

class HttpError extends Error {
  constructor(readonly status: number, message: string) { super(message); }
}
const equal = (left: string, right: string) => /^[a-f0-9]{64}$/.test(left) &&
  /^[a-f0-9]{64}$/.test(right) && crypto.timingSafeEqual(Buffer.from(left), Buffer.from(right));
function json(response: ServerResponse, status: number, body: unknown) {
  response.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8' });
  response.end(JSON.stringify(body));
}
function readJson(request: IncomingMessage): Promise<unknown> {
  if (!/^application\/json(?:\s*;|$)/i.test(request.headers['content-type'] || ''))
    throw new HttpError(415, '请求必须使用 JSON。');
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let bytes = 0, rejected = false;
    request.on('data', chunk => {
      if (rejected) return;
      bytes += chunk.length;
      if (bytes > 160 * 1024) { rejected = true; chunks.length = 0; reject(new HttpError(413, '请求内容过大。')); return; }
      chunks.push(chunk);
    });
    request.on('end', () => {
      if (rejected) return;
      try { resolve(JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(chunks)))); }
      catch { reject(new HttpError(400, 'JSON 内容无效。')); }
    });
    request.on('error', () => reject(new HttpError(400, '请求已中断。')));
  });
}

type Session = { id: string; csrf: string; touchedAt: number };
export function createWebService(config: WebConfig, runner: WebRunner = new DockerWebRunner(config)) {
  const sessions = new Map<string, Session>();
  const jobs = new WebJobs(runner, config);
  const rates = new Map<string, { count: number; expiresAt: number }>();
  const origin = new URL(config.publicUrl);
  const secure = origin.protocol === 'https:';
  const setSessionCookie = (response: ServerResponse, session: Session) => {
    response.setHeader('Set-Cookie', `theoremos_session=${session.id}; Path=/; HttpOnly; SameSite=Strict; Max-Age=${Math.floor(config.sessionTtlMs / 1000)}${secure ? '; Secure' : ''}`);
  };
  const prune = () => {
    for (const [id, session] of sessions) if (Date.now() - session.touchedAt > config.sessionTtlMs) {
      jobs.forget(id); sessions.delete(id);
    }
    for (const [ip, rate] of rates) if (rate.expiresAt <= Date.now()) rates.delete(ip);
  };
  const maintenance = setInterval(prune, 60_000).unref();
  const server = http.createServer(async (request, response) => {
    response.setHeader('Cache-Control', 'no-store');
    response.setHeader('X-Content-Type-Options', 'nosniff');
    response.setHeader('Referrer-Policy', 'no-referrer');
    response.setHeader('X-Frame-Options', 'DENY');
    response.setHeader('Permissions-Policy', 'camera=(), microphone=(), geolocation=()');
    response.setHeader('Content-Security-Policy', "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; font-src 'self'; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'self'");
    if (secure) response.setHeader('Strict-Transport-Security', 'max-age=31536000');
    try {
      if (request.url === '/healthz') { json(response, 200, { ok: true }); return; }
      if (request.headers.host !== origin.host) throw new HttpError(403, '访问地址与服务配置不一致。');
      if (request.headers.origin && request.headers.origin !== origin.origin) throw new HttpError(403, '跨站请求已拒绝。');
      const url = new URL(request.url || '/', origin);
      if (url.origin !== origin.origin) throw new HttpError(403, '访问地址无效。');
      if (url.pathname.startsWith('/api/')) {
        prune();
        const ip = request.socket.remoteAddress || '';
        let rate = rates.get(ip);
        if (!rate) {
          if (rates.size >= 2_000) throw new HttpError(429, '请求较多，请稍后重试。');
          rates.set(ip, rate = { count: 0, expiresAt: Date.now() + 60_000 });
        }
        if (++rate.count > 600) throw new HttpError(429, '请求过于频繁，请稍后重试。');
        const cookie = request.headers.cookie?.split(';').map(value => value.trim()).find(value => value.startsWith('theoremos_session='))?.slice(18);
        let session = cookie ? sessions.get(cookie) : undefined;
        if (request.method === 'GET' && url.pathname === '/api/session') {
          if (!session) {
            if (sessions.size >= 200) throw new HttpError(503, '当前会话数已满，请稍后重试。');
            session = { id: crypto.randomBytes(32).toString('hex'), csrf: crypto.randomBytes(32).toString('hex'), touchedAt: Date.now() };
            sessions.set(session.id, session);
          }
          setSessionCookie(response, session);
          session.touchedAt = Date.now();
          const body: WebSession = { csrfToken: session.csrf, providers: config.providers, environments: getWebEnvironments(),
            templates: webTemplates, defaults: webDefaults, limits: webLimits, runtime: await runner.readiness() };
          json(response, 200, body); return;
        }
        if (!session) throw new HttpError(401, '会话已过期，请刷新页面。');
        session.touchedAt = Date.now();
        if (request.method !== 'GET' && !equal(String(request.headers['x-csrf-token'] || ''), session.csrf))
          throw new HttpError(403, '会话校验失败，请刷新页面。');
        setSessionCookie(response, session);
        if (url.pathname === '/api/runs' && request.method === 'GET') { json(response, 200, { runs: jobs.list(session.id) }); return; }
        if (url.pathname === '/api/runs' && request.method === 'POST') {
          const parsed = inputSchema.safeParse(await readJson(request));
          if (!parsed.success) throw new HttpError(400, '请检查题目、API Key、模型、模块方案及运行预算。');
          const provider = config.providers.find(item => item.id === parsed.data.providerId);
          if (!provider) throw new HttpError(400, '该模型服务尚未配置。');
          if (!(await runner.readiness()).ready) throw new HttpError(503, '运行环境尚未就绪，请先构建 worker 镜像。');
          try { json(response, 201, { run: jobs.create(session.id, parsed.data as WebRunInput, provider) }); }
          catch (error) { throw new HttpError(429, error instanceof Error ? error.message : '运行队列已满。'); }
          return;
        }
        const match = /^\/api\/runs\/([a-f0-9-]{36})(?:\/(cancel|download))?$/.exec(url.pathname);
        if (!match) throw new HttpError(404, '页面或运行不存在。');
        const run = jobs.get(session.id, match[1]);
        if (!run) throw new HttpError(404, '运行不存在或不属于当前会话。');
        if (match[2] === 'cancel' && request.method === 'POST') { json(response, 200, { run: jobs.cancel(session.id, run.id) }); return; }
        if (!match[2] && request.method === 'DELETE') {
          const removed = jobs.remove(session.id, run.id);
          if (removed === 'active') throw new HttpError(409, '排队中或运行中的任务不能删除，请先取消或等待结束。');
          if (removed === 'missing') throw new HttpError(404, '运行不存在或不属于当前会话。');
          json(response, 200, { deletedId: run.id }); return;
        }
        if (match[2] === 'download' && request.method === 'GET') {
          if (!run.result && !['completed', 'cancelled', 'error'].includes(run.status))
            throw new HttpError(409, '运行尚未结束，且结果尚未生成。');
          response.setHeader('Content-Disposition', `attachment; filename="theoremos-${run.id}.json"`);
          json(response, 200, { schema: 'theorem-os.web-export.v1', run }); return;
        }
        if (!match[2] && request.method === 'GET') { json(response, 200, { run }); return; }
        throw new HttpError(405, '请求方法不受支持。');
      }
      if (!['GET', 'HEAD'].includes(request.method || '')) throw new HttpError(405, '请求方法不受支持。');
      const relative = decodeURIComponent(url.pathname).replace(/^\/+/, '') || 'index.html';
      const file = path.resolve(config.staticRoot, relative);
      if (!file.startsWith(config.staticRoot + path.sep) || !fs.existsSync(file) || !fs.lstatSync(file).isFile() || fs.lstatSync(file).isSymbolicLink())
        throw new HttpError(404, '页面不存在，请先运行 bun run build:web。');
      if (!fs.realpathSync(file).startsWith(fs.realpathSync(config.staticRoot) + path.sep))
        throw new HttpError(404, '文件不存在。');
      const allowed: Record<string, string> = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
        '.css': 'text/css; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.woff2': 'font/woff2', '.txt': 'text/plain; charset=utf-8' };
      const contentType = allowed[path.extname(file)];
      if (!contentType) throw new HttpError(404, '文件不存在。');
      response.writeHead(200, { 'Content-Type': contentType });
      if (request.method === 'HEAD') response.end();
      else fs.createReadStream(file).on('error', () => response.destroy()).pipe(response);
    } catch (error) {
      if (!response.headersSent) json(response, error instanceof HttpError ? error.status : 500,
        { error: error instanceof HttpError ? error.message : '服务暂时不可用。' });
      else response.end();
    }
  });
  server.requestTimeout = 15_000; server.headersTimeout = 10_000;
  const close = async () => {
    clearInterval(maintenance);
    server.closeIdleConnections();
    await Promise.all([jobs.close(), new Promise<void>(resolve => server.close(() => resolve()))]);
  };
  return { server, jobs, close };
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const config = readWebConfig();
  const service = createWebService(config);
  service.server.listen(config.port, config.host, () => console.log(`TheoremOS workbench: ${config.publicUrl}`));
  let stopping = false;
  const stop = () => { if (!stopping) { stopping = true; void service.close().then(() => process.exit(0)); } };
  process.once('SIGINT', stop); process.once('SIGTERM', stop);
}
