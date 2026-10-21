import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import { configurableSolverModules } from '../src/solver/modules/custom';
import type { ContextAccess } from '../src/solver/modules/context';
import { configuredSolverModules, directSolverModules, solverMethodDigest } from '../src/solver/modules';
import { defaultResearchModulePlan, researchModulePlanDraftSchema, researchModulePlanSchema,
  type CustomResearchModule, type ResearchModulePlan, type ResearchModuleSlot } from '../src/solver/modules/policy';
import type { SolverProblem } from '../src/solver/problem';
import type { StatementAction, StatementReview } from '../src/solver/statementReview';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

const custom = (slot: ResearchModuleSlot = 'M1', overrides: Partial<CustomResearchModule> = {}): CustomResearchModule => ({
  id: `custom-${slot}`, name: `My ${slot} strategy`, slot, mode: 'append', enabled: true,
  instructions: `CUSTOM_${slot}_INSTRUCTIONS`, ...overrides,
});
const plan = (custom: CustomResearchModule[] = [], overrides: Partial<ResearchModulePlan> = {}): ResearchModulePlan =>
  ({ ...defaultResearchModulePlan(), custom, ...overrides });
const formal = 'namespace Original\nvariable (n : Nat)\ntheorem target (h : n > 0) : n > 0 := by sorry\nend Original';
const problem = { projectRelative: 'generated/p', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: 'target (h : n > 0) : n > 0' }] },
  sourceImports: { 'Submission.lean': ['Mathlib.Data.Nat.Basic'] },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: 'original-type' }],
  receiptDigest: 'fixed-problem-receipt', baseCommit: 'fixed-source-commit',
  contract: { formalStatement: formal, assumptions: ['n is a natural number', 'n > 0'],
    statementHash: 'fixed-statement', leanStatementHash: 'fixed-lean-statement' } } as unknown as SolverProblem;
const state = (overrides: Partial<SolverRunState> = {}): SolverRunState => ({
  phase: 'running', turns: 0, environmentDigest: 'fixed-environment', ...overrides,
} as SolverRunState);
const access = (overrides: Partial<ContextAccess> = {}): ContextAccess => ({
  root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the original target.', retrievalRoot: '/library',
  frozenContexts: { 'Submission.lean': 'namespace Original\nvariable (n : Nat)\ntheorem target (h : n > 0) : n > 0 := /- body omitted -/\nend Original' },
  ...overrides,
});

afterEach(() => vi.restoreAllMocks());

describe('browser-safe research module policy', () => {
  it('returns fresh default plans and preserves editable draft text', () => {
    const first = defaultResearchModulePlan(), second = defaultResearchModulePlan();
    first.custom.push(custom());
    expect(second).toEqual({ scheduler: 'plan', context: 'full', custom: [] });
    const draft = plan([custom('M1', { name: '', instructions: '' }),
      custom('M1', { id: 'second', name: '  Name in progress  ', mode: 'replace', instructions: '\n  ' }),
      custom('M1', { id: 'third', mode: 'replace' })]);
    expect(researchModulePlanDraftSchema.parse(draft)).toEqual(draft);
    expect(researchModulePlanSchema.safeParse(draft).success).toBe(false);
    const saved = plan([custom('M1', { name: '  Named module  ', instructions: '\nRule text.\n' })]);
    expect(researchModulePlanSchema.parse(saved)).toEqual(saved);
  });

  it('requires named modules, enabled instructions and one enabled replacement per slot only on submission', () => {
    expect(researchModulePlanSchema.safeParse(plan([custom('M1', { name: '  ' })])).success).toBe(false);
    expect(researchModulePlanSchema.safeParse(plan([custom('M1', { instructions: '\n\t ' })])).success).toBe(false);
    expect(researchModulePlanSchema.safeParse(plan([custom('M1', { enabled: false, instructions: '' })])).success).toBe(true);
    const conflict = plan([custom('M1', { mode: 'replace' }), custom('M1', { id: 'second', mode: 'replace' })]);
    expect(researchModulePlanDraftSchema.safeParse(conflict).success).toBe(true);
    expect(researchModulePlanSchema.safeParse(conflict).success).toBe(false);
    conflict.custom[1].enabled = false;
    expect(researchModulePlanSchema.safeParse(conflict).success).toBe(true);
    expect(researchModulePlanSchema.safeParse(plan([custom('M1', { mode: 'replace' }), custom('M4', { mode: 'replace' })])).success).toBe(true);
  });

  it('measures both individual and aggregate rule limits in UTF-8 bytes including disabled rules', () => {
    const fourThousand = '证'.repeat(1_333) + 'x';
    expect(Buffer.byteLength(fourThousand)).toBe(4_000);
    const maximum = plan(Array.from({ length: 4 }, (_, index) => custom('M1', { id: `rule-${index}`, instructions: fourThousand })));
    expect(researchModulePlanSchema.safeParse(maximum).success).toBe(true);
    maximum.custom.push(custom('M1', { id: 'one-extra-byte', instructions: 'x', enabled: false }));
    expect(researchModulePlanDraftSchema.safeParse(maximum).success).toBe(false);
    expect(researchModulePlanDraftSchema.safeParse(plan([custom('M1', { instructions: fourThousand + 'x' })])).success).toBe(false);
  });

  it.each([
    { ...plan(), extra: 'unknown' }, plan([{ ...custom(), path: '/private' } as CustomResearchModule]),
    plan([custom('M1', { id: '../module' })]), plan([custom('M1', { id: '__proto__' })]),
    plan([custom('M1', { name: 'x'.repeat(41) })]), plan([custom('M1', { name: 'bad\0name' })]),
    plan([custom('M1', { instructions: 'bad\0rule' })]), plan([custom('M1', { slot: 'M2' as ResearchModuleSlot })]),
    plan([custom('M1', { mode: 'execute' as 'append' })]), plan([custom('M1', { enabled: 'yes' as unknown as boolean })]),
    plan([custom(), custom()]), plan(Array.from({ length: 9 }, (_, index) => custom('M1', { id: `rule-${index}` }))),
    plan([], { scheduler: 'custom-code' as 'plan' }), plan([], { context: 'none' as 'full' }),
  ])('rejects malformed or unbounded configuration at the draft boundary (%#)', value => {
    expect(researchModulePlanDraftSchema.safeParse(value).success).toBe(false);
    expect(() => configurableSolverModules(value)).toThrow();
  });

  it('bundles the shared policy for browsers without loading solver or Node dependencies', async () => {
    const bundled = await build({ entryPoints: [fileURLToPath(new URL('../src/solver/modules/policy.ts', import.meta.url))],
      bundle: true, platform: 'browser', format: 'esm', write: false, logLevel: 'silent', metafile: true });
    expect(Object.keys(bundled.metafile!.inputs).some(file => file.includes('src/solver/modules/index'))).toBe(false);
    expect(bundled.outputFiles[0].text).toContain('researchModulePlanSchema');
  });
});

describe('configured solver strategy rules without inference or Lean calls', () => {
  it('preserves default module identities and composes existing scheduler presets', () => {
    expect(configurableSolverModules()).toBe(directSolverModules);
    expect(configurableSolverModules(defaultResearchModulePlan())).toBe(directSolverModules);
    expect(configurableSolverModules(plan([custom('M1', { enabled: false })]))).toBe(directSolverModules);
    for (const scheduler of ['goals-first', 'critical-path', 'continuation'] as const) {
      const actual = configurableSolverModules(plan([], { scheduler }));
      const expected = configuredSolverModules('direct', scheduler);
      expect(actual.M3.ready).toBe(expected.M3.ready);
      expect(actual.M5.assign).toBe(expected.M5.assign);
      expect(solverMethodDigest(actual, 'cooperative')).toBe(solverMethodDigest(expected, 'cooperative'));
    }
  });

  it('appends to or replaces the selected strategy while preserving mathematical and source contracts', () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const fallback = 'Use installed library lemmas and test uncertain bridges early.';
    const appended = configurableSolverModules(plan([custom()])).M4.build(problem, state(), access());
    const replaced = configurableSolverModules(plan([custom('M1', { mode: 'replace' })])).M4.build(problem, state(), access());
    expect(appended.instructions).toContain(fallback);
    expect(appended.instructions).toContain('CUSTOM_M1_INSTRUCTIONS');
    expect(replaced.instructions).not.toContain(fallback);
    expect(replaced.instructions).toContain('CUSTOM_M1_INSTRUCTIONS');
    for (const context of [appended, replaced]) {
      expect(context.instructions).toContain('Preserve original declaration kinds, names, parameters, types, assumptions');
      expect(context.instructions).toContain('Completed proofs must not use sorry, admit, native_decide, unsafe or new axioms.');
      expect(context.instructions).toContain('check-lean');
      expect(context.instructions).toContain('Then return for independent host checking.');
      expect(context.message).toContain(formal);
      expect(context.message).toContain('n is a natural number');
      expect(context.sources.problemReceiptDigest).toBe(problem.receiptDigest);
    }
  });

  it('keeps exact role output protocols when every optional strategy slot is replaced', () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const configuration = plan((['M1', 'M3', 'M4', 'M5'] as const).map(slot => custom(slot, { mode: 'replace' })));
    const modules = configurableSolverModules(configuration, 'cooperative', 4);
    const context = modules.M4.build(problem, state({ cooperation: { tasks: [] } }),
      access({ assignment: { kind: 'lead', seedCommit: 'fixed-source-commit' } }));
    for (const slot of ['M1', 'M3', 'M4', 'M5']) expect(context.instructions).toContain(`CUSTOM_${slot}_INSTRUCTIONS`);
    expect(context.instructions).toContain('You are the Lead.');
    expect(context.instructions).toContain('Write one JSON object in RESEARCH.md: {"tasks":');
    expect(context.instructions).toContain('Include every original target once.');
    expect(context.instructions).toContain('Exact mathematical interfaces and original assumptions are mandatory');
    expect(context.instructions).toContain('Unproved dependencies and reviews remain advisory.');
    expect(context.instructions).not.toContain('Repair the earliest error; avoid rebuilding dependencies or repeating unchanged checks.');
    expect(context.instructions).not.toContain('Keep this file as a concise current checkpoint; replace obsolete status');
  });

  it.each(['full', 'essential'] as const)('retains pinned knowledge tools with replaced strategies and %s context', contextMode => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const knowledge = { digest: mathDigest('pinned-catalog'),
      base: { entries: [], evidence: 'recorded-not-replayed' as const } };
    const modules = configurableSolverModules(plan([
      custom('M1', { mode: 'replace' }), custom('M4', { mode: 'replace' }),
    ], { context: contextMode }));
    const context = modules.M4.build(problem, state({ problem }), access({ knowledgeFile: '/catalog/pinned.json',
      knowledgeDigest: knowledge.digest, knowledgeSnapshot: knowledge }));
    expect(context.instructions).toContain('CUSTOM_M1_INSTRUCTIONS');
    expect(context.instructions).toContain('CUSTOM_M4_INSTRUCTIONS');
    expect(context.instructions).not.toContain('Use installed library lemmas and test uncertain bridges early.');
    expect(context.instructions).toContain('knowledge get');
    expect(context.instructions).toContain('--metadata --max-bytes 16000');
    expect(context.instructions).toContain('knowledge dependencies');
    expect(context.instructions).toContain('knowledge source');
    expect(context.instructions).toContain('Never copy an entire archived Submission over current goals or inherit historical receipts.');
    expect(context.message).toContain(formal);
    expect(context.message).toContain('n is a natural number');
    if (contextMode === 'full') {
      expect(context.message).toContain('Saved theorem candidates');
      expect(context.message).toContain(knowledge.digest);
      expect(context.manifest?.included).toContainEqual(expect.objectContaining({
        id: expect.stringMatching(/^knowledge:/u), required: false,
      }));
    } else {
      expect(context.message).not.toContain('Saved theorem candidates');
      expect(context.manifest?.omitted).toContainEqual({
        id: expect.stringMatching(/^knowledge:/u), kind: 'sources', reason: 'optional-budget',
      });
    }
  });

  it('binds all applied instructions into the actual manifest digest and total byte budget', () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const modules = configurableSolverModules(plan([custom('M1', { instructions: '使用固定类型，再检查候选。' })]));
    const context = modules.M4.build(problem, state(), access());
    const content = context.message.split('\n\nContext compilation manifest:\n')[0];
    expect(context.manifest?.contentDigest).toBe(mathDigest(JSON.stringify({ instructions: context.instructions, message: content })));
    expect(context.manifest?.usedBytes).toBe(Buffer.byteLength(context.instructions) + Buffer.byteLength(context.message));
    const baseline = directSolverModules.M4.build(problem, state(), access());
    expect(context.manifest?.contentDigest).not.toBe(baseline.manifest?.contentDigest);
    const large = configurableSolverModules(plan([custom('M1', { instructions: 'x'.repeat(4_000) })]));
    expect(() => large.M4.build(problem, state(), access({ maxContextBytes: baseline.manifest!.mandatoryBytes + 100 })))
      .toThrow('math_context_mandatory_overflow');
  });

  it('keeps mandatory dependency interfaces and original mathematics in essential context while omitting advisory material', () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const prerequisite: CooperativeTask = { id: 'base', kind: 'lemma', objective: 'Prove base', dependsOn: [], revision: 0,
      theoremName: 'Original.base', proofPath: 'Submission.lean', type: '∀ n : Nat, n = n' };
    const consumer: CooperativeTask = { ...prerequisite, id: 'consumer', theoremName: 'Original.consumer', dependsOn: ['base'] };
    const context = configurableSolverModules(plan([custom('M4')], { context: 'essential' })).M4.build(problem,
      state({ cooperation: { tasks: [{ task: consumer, status: 'pending', attempts: 0 },
        { task: prerequisite, status: 'pending', attempts: 0, finding: 'ADVISORY_FINDING' }] } }),
      access({ sourceFeedback: 'CURRENT_HOST_DIAGNOSTIC', assignment: { kind: 'task', task: consumer,
        assignment: { taskId: consumer.id, taskDigest: taskVersion(consumer), workerId: 'researcher-1', seedCommit: 'fixed-source-commit' } } }));
    expect(context.manifest?.maxOptionalBytes).toBe(0);
    expect(context.manifest?.optionalBytes).toBe(0);
    expect(context.manifest?.requiredTaskIds).toEqual(['consumer', 'base']);
    expect(context.manifest?.included.find(item => item.id === 'task-interfaces')?.required).toBe(true);
    expect(context.message).toContain(formal);
    expect(context.message).toContain(prerequisite.type);
    expect(context.message).toContain('n is a natural number');
    expect(context.message).toContain('generated/p/Submission.lean');
    expect(context.message).not.toContain('ADVISORY_FINDING');
    expect(context.message).toContain('CURRENT_HOST_DIAGNOSTIC');
    expect(context.manifest?.included.find(item => item.id === 'current-feedback')?.required).toBe(true);
    expect(context.instructions).toContain('CUSTOM_M4_INSTRUCTIONS');
    expect(context.manifest?.omitted).toContainEqual({ id: 'finding:base', kind: 'finding', reason: 'optional-budget' });
  });

  it('leaves blind fixed-statement review and checkers unchanged', () => {
    const log = vi.spyOn(console, 'log').mockImplementation(() => {});
    const modules = configurableSolverModules(plan([custom('M1'), custom('M4', { instructions: 'PRIVATE_TASK_STRATEGY' })]));
    expect(modules.M4.statement).toBe(directSolverModules.M4.statement);
    expect(modules.M2).toBe(directSolverModules.M2);
    expect(modules.M1.open).toBe(directSolverModules.M1.open);
    expect(modules.M1.execute).toBe(directSolverModules.M1.execute);
    const review = { intendedStatement: 'PRIVATE_INTENDED_MATHEMATICS', premises: ['PRIVATE_PREMISE'] } as unknown as StatementReview;
    const action = { kind: 'backtranslate', taskId: 'goal' } as StatementAction;
    const context = modules.M4.statement(review, action, problem.receiptDigest);
    expect(context.scope).toBe('fixed-statement');
    expect(context.message).not.toMatch(/PRIVATE_TASK_STRATEGY|PRIVATE_INTENDED_MATHEMATICS|PRIVATE_PREMISE/);
    expect(context.instructions).not.toContain('CUSTOM_M1_INSTRUCTIONS');
    expect(log).not.toHaveBeenCalled();
  });

  it('binds enabled content, slot, mode, context and scheduler to method identity while ignoring disabled edits', () => {
    const baseVersion = directSolverModules.M1.version;
    const original = plan([custom()]);
    const digest = (value: ResearchModulePlan) => solverMethodDigest(configurableSolverModules(value), 'cooperative');
    const baseline = digest(original);
    for (const change of [
      (value: ResearchModulePlan) => { value.custom[0].instructions += '\nChanged rule.'; },
      (value: ResearchModulePlan) => { value.custom[0].name = 'Renamed'; },
      (value: ResearchModulePlan) => { value.custom[0].mode = 'replace'; },
      (value: ResearchModulePlan) => { value.custom[0].slot = 'M4'; },
      (value: ResearchModulePlan) => { value.context = 'essential'; },
      (value: ResearchModulePlan) => { value.scheduler = 'continuation'; },
      (value: ResearchModulePlan) => { value.custom[0].enabled = false; },
    ]) {
      const changed = structuredClone(original); change(changed);
      expect(digest(changed)).not.toBe(baseline);
    }
    const disabled = plan([custom('M4', { enabled: false })]);
    const before = digest(disabled);
    disabled.custom[0].name = 'Different disabled name'; disabled.custom[0].instructions = 'Different disabled rule';
    expect(digest(disabled)).toBe(before);
    expect(directSolverModules.M1.version).toBe(baseVersion);
  });

  it('orders rules within each module and ignores disabled positions without moving module sections', () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const first = custom('M1', { id: 'ordered-a', instructions: 'ORDERED_RULE_A' });
    const middle = custom('M4', { id: 'ordered-b', instructions: 'ORDERED_RULE_B' });
    const last = custom('M1', { id: 'ordered-c', instructions: 'ORDERED_RULE_C' });
    const disabled = custom('M3', { id: 'ordered-disabled', enabled: false, instructions: 'DISABLED_RULE' });
    const original = configurableSolverModules(plan([first, middle, last, disabled]));
    const reordered = configurableSolverModules(plan([last, middle, first, disabled]));
    const originalContext = original.M4.build(problem, state(), access());
    const reorderedContext = reordered.M4.build(problem, state(), access());
    expect(originalContext.instructions.match(/ORDERED_RULE_[ABC]/g)).toEqual([
      'ORDERED_RULE_A', 'ORDERED_RULE_C', 'ORDERED_RULE_B',
    ]);
    expect(reorderedContext.instructions.match(/ORDERED_RULE_[ABC]/g)).toEqual([
      'ORDERED_RULE_C', 'ORDERED_RULE_A', 'ORDERED_RULE_B',
    ]);
    expect(solverMethodDigest(reordered, 'cooperative')).not.toBe(solverMethodDigest(original, 'cooperative'));
    expect(reorderedContext.manifest?.contentDigest).not.toBe(originalContext.manifest?.contentDigest);
    const movedDisabled = configurableSolverModules(plan([disabled, first, middle, last]));
    expect(solverMethodDigest(movedDisabled, 'cooperative')).toBe(solverMethodDigest(original, 'cooperative'));
    const movedDisabledContext = movedDisabled.M4.build(problem, state(), access());
    expect(movedDisabledContext.instructions).toBe(originalContext.instructions);
    expect(movedDisabledContext.manifest?.contentDigest).toBe(originalContext.manifest?.contentDigest);
    expect(movedDisabledContext.instructions).not.toContain('DISABLED_RULE');
  });

  it('captures a validated configuration rather than reading later edits to the draft', () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const draft = plan([custom()]);
    const modules = configurableSolverModules(draft);
    const digest = solverMethodDigest(modules, 'cooperative');
    draft.custom[0].instructions = 'LATER_DRAFT_EDIT'; draft.custom[0].enabled = false;
    const context = modules.M4.build(problem, state(), access());
    expect(context.instructions).toContain('CUSTOM_M1_INSTRUCTIONS');
    expect(context.instructions).not.toContain('LATER_DRAFT_EDIT');
    expect(solverMethodDigest(modules, 'cooperative')).toBe(digest);
  });

  it('applies M5 rules only when multiple cooperative workers actually have a cooperation context', () => {
    const log = vi.spyOn(console, 'log').mockImplementation(() => {});
    const configuration = plan([custom('M5')]);
    expect(configurableSolverModules(configuration, 'independent', 4)).toBe(directSolverModules);
    expect(configurableSolverModules(configuration, 'cooperative', 1)).toBe(directSolverModules);
    const modules = configurableSolverModules(configuration, 'cooperative', 2);
    const noCooperation = modules.M4.build(problem, state(), access());
    expect(noCooperation.instructions).not.toContain('CUSTOM_M5_INSTRUCTIONS');
    expect(log).not.toHaveBeenCalled();
    const cooperative = modules.M4.build(problem, state({ cooperation: { tasks: [] } }), access());
    expect(cooperative.instructions).toContain('CUSTOM_M5_INSTRUCTIONS');
    expect(log).toHaveBeenCalledTimes(1);
  });

  it('emits bounded rule application observations only after successful compilation, without private text', () => {
    const log = vi.spyOn(console, 'log').mockImplementation(() => {});
    const rule = custom('M4', { name: 'PRIVATE_NAME', instructions: 'PRIVATE_RULE_BODY' });
    const modules = configurableSolverModules(plan([rule, custom('M1', { enabled: false })]));
    modules.M4.build(problem, state(), access());
    modules.M4.build(problem, state(), access());
    expect(log).toHaveBeenCalledTimes(2);
    for (const [line] of log.mock.calls) {
      expect(JSON.parse(line as string)).toEqual({ event: 'custom_module_applied', at: expect.any(Number),
        moduleId: rule.id, slot: rule.slot, mode: rule.mode });
      expect(line).not.toMatch(/PRIVATE_NAME|PRIVATE_RULE_BODY|CUSTOM_M1_INSTRUCTIONS/);
    }
    log.mockClear();
    expect(() => modules.M4.build(problem, state(), access({ maxContextBytes: 100 }))).toThrow('math_context_mandatory_overflow');
    expect(log).not.toHaveBeenCalled();
  });
});
