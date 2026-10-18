import { describe, expect, it } from 'vitest';
import { defaultResearchModulePlan, type CustomResearchModule, type ResearchModulePlan } from '../src/solver/modules/policy';
import { directSolverModules, solverMethodDigest } from '../src/solver/modules';
import { decodeTaskDraft, encodeTaskDraft, type TaskDraft } from '../apps/web/client/draft';
import { DraftRecovery } from '../apps/web/client/draftRecovery';
import { customModuleState } from '../apps/web/client/moduleView';
import { isWebEventDetails, recordWebModuleEvent, webCustomModuleSnapshots } from '../apps/web/moduleTelemetry';
import { translateWebProgress } from '../apps/web/progress';
import { parseWorkerMessage } from '../apps/web/runner';
import { webSolverModules } from '../apps/web/worker';
import type { WebEvent, WebRun, WorkerInput } from '../apps/web/shared';

const rule = (overrides: Partial<CustomResearchModule> = {}): CustomResearchModule => ({
  id: 'my-strategy', name: 'My proof strategy', slot: 'M1', mode: 'append', enabled: true,
  instructions: 'Prefer a short proof using library lemmas.', ...overrides,
});
const plan = (...rules: CustomResearchModule[]): ResearchModulePlan => ({ ...defaultResearchModulePlan(), custom: rules });
const draft = (modulePlan?: ResearchModulePlan): TaskDraft => ({
  providerId: 'openai', model: 'fixture', effort: 'low', environment: 'standard', coordination: 'cooperative',
  source: 'theorem target : True := by sorry', task: 'Prove the original target.',
  maxTurns: '2', maxRunSeconds: '60', workers: '2', templateId: '', ...(modulePlan ? { modulePlan } : {}),
});
const at = '2026-10-18T12:00:00.000Z';
const run = (modulePlan = plan(rule()), changes: Partial<WebRun> = {}): WebRun => ({
  ...draft(modulePlan), id: 'module-plan-fixture', title: 'A theorem', status: 'running', phase: 'solve_started',
  maxTurns: 2, maxRunSeconds: 60, workers: 2, events: [], createdAt: at, updatedAt: at, ...changes,
});
const event = (sequence = 1, changes: Partial<WebEvent['details']> = {}): WebEvent => ({
  sequence, at, type: 'custom_module_applied', message: 'Rule included in compiled context',
  details: { moduleId: 'my-strategy', slot: 'M1', mode: 'append', ...changes },
});

describe('web module plan persistence and worker boundary', () => {
  it('round trips complete and unfinished plans through drafts and archived runs', () => {
    const configured = { ...plan(rule()), scheduler: 'goals-first' as const, context: 'essential' as const };
    for (const value of [configured, plan(rule({ name: '', instructions: '' })), undefined]) {
      const saved = draft(value);
      expect(decodeTaskDraft(JSON.parse(encodeTaskDraft(saved)))).toEqual(saved);
      const archived = run(value);
      if (!value) delete archived.modulePlan;
      const imported = decodeTaskDraft({ schema: 'theorem-os.web-export.v1', run: archived });
      expect(imported.modulePlan).toEqual(value);
    }
  });

  it('rejects executable plugin fields or malformed plans in imported drafts', () => {
    for (const modulePlan of [null, { ...plan(), path: '/plugin.ts' }, plan({ ...rule(), apiKey: 'not-a-module-field' } as CustomResearchModule)]) {
      expect(() => decodeTaskDraft({ schema: 'theorem-os.web-draft.v1', draft: { ...draft(), modulePlan } })).toThrow('任务草稿格式无效');
    }
  });

  it('keeps a deep snapshot in draft recovery independently of later editor changes', () => {
    const values = new Map<string, string>(), storage = {
      getItem: (key: string) => values.get(key) ?? null,
      setItem: (key: string, value: string) => { values.set(key, value); }, removeItem: (key: string) => { values.delete(key); },
    };
    const before = draft(plan(rule())), recovery = new DraftRecovery(() => storage);
    recovery.remember(before, draft(), 'reset');
    before.modulePlan!.custom[0].instructions = 'A later edit';
    recovery.current!.draft.modulePlan!.custom[0].enabled = false;
    const restored = new DraftRecovery(() => storage); restored.load();
    expect(restored.current!.draft.modulePlan).toEqual(plan(rule()));
    expect(recovery.current!.draft.modulePlan).toEqual(plan(rule()));
    expect([...values.values()].join('')).not.toContain('apiKey');
  });

  it('composes BYOK with the configured scheduler without replacing Lean checks or fixed statement review', () => {
    const request: WorkerInput = { id: 'fixture', provider: { id: 'openai', name: 'Fixture', baseUrl: 'https://example.invalid/v1' },
      input: { ...run(plan(rule()), { modulePlan: { ...plan(rule()), scheduler: 'critical-path' } }), apiKey: 'sk-fixture-no-network' } };
    const configured = webSolverModules(request);
    expect(configured.M3.ready).not.toBe(directSolverModules.M3.ready);
    expect(configured.M2).toBe(directSolverModules.M2);
    expect(configured.M4.statement).toBe(directSolverModules.M4.statement);
    const method = solverMethodDigest(configured, 'cooperative');
    request.input.modulePlan!.custom[0].enabled = false;
    expect(solverMethodDigest(webSolverModules(request), 'cooperative')).not.toBe(method);
    expect(JSON.stringify(configured)).not.toContain('sk-fixture-no-network');
  });
});

describe('observed custom module applications', () => {
  it('translates only application identity and rejects executable, private or invalid protocol fields', () => {
    const message = translateWebProgress({ event: 'custom_module_applied', moduleId: 'my-strategy', slot: 'M1', mode: 'append',
      instructions: 'PRIVATE_RULE_TEXT', path: '/private/path', apiKey: 'PRIVATE_KEY' })!;
    expect(message).toEqual({ type: 'progress', event: 'custom_module_applied', message: '已将自定义策略加入本轮上下文',
      details: { moduleId: 'my-strategy', slot: 'M1', mode: 'append' } });
    expect(parseWorkerMessage(JSON.stringify(message))).toEqual(message);
    expect(isWebEventDetails({ moduleId: '__proto__' })).toBe(false);
    expect(isWebEventDetails({ slot: 'M2' })).toBe(false);
    expect(isWebEventDetails({ mode: 'execute' })).toBe(false);
    expect(parseWorkerMessage(JSON.stringify({ ...message, details: { ...message.details, instructions: 'private' } }))).toBeUndefined();
  });

  it('retains cumulative applications independently of the event window without inferring a model call or acceptance', () => {
    const value = run();
    for (let index = 1; index <= 5; index++) recordWebModuleEvent(value, event(index));
    expect(value.modules).toEqual({});
    expect(webCustomModuleSnapshots(value)['my-strategy']).toMatchObject({ eventCount: 5, activeWorkers: [], lastEvent: { sequence: 5 } });
    expect(value.events).toEqual([]);
    expect(value.result).toBeUndefined();
    expect(customModuleState(rule(), { run: value, coordination: value.coordination, workers: value.workers }, value.moduleApplications!['my-strategy']))
      .toBe('已应用 5 次');
    const legacy = run(plan(rule()), { events: [event(1), event(2)] });
    expect(webCustomModuleSnapshots(legacy)['my-strategy'].eventCount).toBe(2);
  });

  it('ignores unknown, disabled, mismatched and currently inapplicable module identities', () => {
    for (const value of [run(plan(rule({ enabled: false }))), run(plan(rule({ slot: 'M4' }))), run(plan(rule({ mode: 'replace' }))), run(plan())]) {
      recordWebModuleEvent(value, event());
      expect(value.moduleApplications).toEqual({});
    }
    for (const changes of [{ coordination: 'independent' as const }, { workers: 1 }]) {
      const value = run(plan(rule({ slot: 'M5' })), changes);
      recordWebModuleEvent(value, event(1, { slot: 'M5' }));
      expect(value.moduleApplications).toEqual({});
      expect(customModuleState(rule({ slot: 'M5' }), { run: value, coordination: value.coordination, workers: value.workers }))
        .toBe('当前模式不参与');
    }
    expect(customModuleState(rule({ enabled: false }), { coordination: 'cooperative', workers: 2 })).toBe('已停用');
    expect(customModuleState(rule(), { coordination: 'cooperative', workers: 2 })).toBe('待应用');
    const finished = run(plan(rule()), { status: 'completed' });
    expect(customModuleState(rule(), { run: finished, coordination: finished.coordination, workers: finished.workers })).toBe('无应用记录');
  });
});
