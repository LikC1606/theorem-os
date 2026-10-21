import type { WebCoordination, WebEvent, WebModuleId, WebModuleSnapshot, WebRun } from '../shared';
import { webCustomModuleSnapshots, webEventModule, webModuleSnapshots } from '../moduleTelemetry';
import { isAcceptedRun, runProgress } from '../presentation';
import { defaultResearchModulePlan, type CustomResearchModule, type ResearchModulePlan } from '../../../src/solver/modules/policy';

const modules = [
  { id: 'M5', name: '协作与复用', subject: '任务分配 · 审阅 · 集成', icon: 'network' },
  { id: 'M3', name: '搜索决策', subject: '任务选择与重试', icon: 'git-branch' },
  { id: 'M4', name: '上下文选择', subject: '题目与研究证据', icon: 'list' },
  { id: 'M2', name: '检查与反馈', subject: 'Lean 检查与诊断', icon: 'circle-check' },
  { id: 'M1', name: '证明构造', subject: '模型生成候选', icon: 'cpu' },
  { id: 'S3', name: '独立验收', subject: '完整原题 · 固定验收', icon: 'shield-check' },
] as const;
type ModuleTone = 'pending' | 'active' | 'observed' | 'feedback' | 'passed' | 'failed' | 'stopped';
type ModuleState = { tone: ModuleTone; label: string };
export type ModuleViewInput = {
  id: string;
  run?: WebRun;
  model: string;
  workers: number;
  coordination: WebCoordination;
  environment: string;
  connected: boolean;
  editable?: boolean;
  modulePlan?: ResearchModulePlan;
};

const schedulers: Record<string, string> = { plan: '按计划', 'critical-path': '关键路径优先', continuation: '延续已有进展' };

export function customModuleState(rule: CustomResearchModule, input: Pick<ModuleViewInput, 'run' | 'coordination' | 'workers'>,
  snapshot?: WebModuleSnapshot): string {
  if (!rule.enabled) return '已停用';
  if (rule.slot === 'M5' && (input.coordination !== 'cooperative' || input.workers <= 1)) return '当前模式不参与';
  if (snapshot) return `已应用 ${snapshot.eventCount} 次`;
  return input.run && !['running', 'queued'].includes(input.run.status) ? '无应用记录' : '待应用';
}

export function latestModuleActivity(snapshots: Partial<Record<WebModuleId, WebModuleSnapshot>>) {
  let latest: { id: WebModuleId; event: WebEvent } | undefined;
  for (const { id } of modules) {
    const event = snapshots[id]?.lastEvent;
    if (event && (!latest || event.sequence > latest.event.sequence)) latest = { id, event };
  }
  return latest;
}

export function moduleState(id: WebModuleId, run?: WebRun, snapshot?: WebModuleSnapshot): ModuleState {
  if (!run) return { tone: 'pending', label: '未运行' };
  const terminal = run.status !== 'running' && run.status !== 'queued';
  const last = snapshot?.lastEvent;
  if (id === 'S3') {
    if (isAcceptedRun(run)) return { tone: 'passed', label: '验收通过' };
    if (run.status === 'completed' && ['evaluated_failed', 'evaluated_rejected'].includes(run.result?.status ?? ''))
      return { tone: 'failed', label: run.result?.status === 'evaluated_rejected' ? '验收拒绝' : '验收未通过' };
    if (last?.type === 'evaluation_finished') return { tone: 'observed', label: terminal ? '尚未验收通过' : '等待结果确认' };
    if (last || run.timings?.evaluating) return terminal
      ? { tone: 'stopped', label: '验收已中断' } : { tone: 'active', label: '独立验收中' };
    return { tone: 'pending', label: terminal ? '无验收记录' : '等待候选' };
  }
  if (!snapshot) return { tone: 'pending', label: run.status === 'queued' ? '等待运行'
    : runProgress(run).index < 2 && !terminal ? '等待研究' : '无活动记录' };
  const researching = !terminal && runProgress(run).index < 3;
  if (snapshot.activeWorkers.length && researching)
    return { tone: 'active', label: id === 'M2' ? '检查中' : '构造中' };
  if (terminal && snapshot.activeWorkers.length) return { tone: 'stopped', label: '已停止' };
  if (id === 'M1') return ['turn_failed', 'worker_failed'].includes(last!.type)
    ? { tone: 'feedback', label: '尝试未完成' } : { tone: 'observed', label: '已有执行记录' };
  if (id === 'M2') {
    if (last?.type === 'source_rejected') return { tone: 'feedback', label: '约束拒绝' };
    if (last?.details?.passed === false) return { tone: 'feedback', label: '待修复' };
    if (last?.details?.passed === true) return { tone: 'observed', label: last.details.conditional ? '条件性通过'
      : last.type === 'proof_checked' ? '候选通过' : '局部通过' };
    return { tone: 'observed', label: '已有检查记录' };
  }
  if (id === 'M5') {
    if (last?.type === 'plan_rejected') return { tone: 'feedback', label: '计划待调整' };
    const labels: Record<string, string> = { plan_updated: '已更新计划', initial_plan_fallback: '已建立计划',
      assembly_started: '集成已启动', review_requested: '已请求审阅', statement_review_requested: '已请求审阅',
      task_assigned: '已分配', review_assigned: '已分配', statement_review_assigned: '已分配',
      review_completed: '已审阅', statement_review_completed: '已审阅', task_integrated: '已集成',
      delivery_published: '已有交接', research_delivered: '已有交接' };
    return { tone: 'observed', label: labels[last!.type] ?? '已有协作记录' };
  }
  return { tone: 'observed', label: id === 'M3' ? last?.type === 'turn_retry' ? '已安排重试' : '已决策'
    : last?.type === 'context_restarted' ? '已重建' : '已整理' };
}

function text(target: Element, value: string) {
  if (target.textContent !== value) target.textContent = value;
}
const timestamp = (value: string) => Number.isFinite(Date.parse(value))
  ? new Intl.DateTimeFormat('zh-CN', { hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false }).format(new Date(value)) : value;
const bytes = (value: number) => value < 1024 ? `${value} B` : `${(value / 1024).toFixed(1)} KB`;
const operations = { direct: '直接证明', decompose: '分解任务', bridge: '检查引理连接', 'prove-lemma': '证明辅助引理', 'integrate-lemma': '集成辅助引理' };
const node = (id: WebModuleId) => {
  const module = modules.find(module => module.id === id)!;
  return `<button type="button" class="module-node" data-module-id="${id}" data-tone="pending" aria-pressed="false" aria-controls="module-inspector">
    <span class="module-node-top"><span class="module-code mono">${id}</span><i data-lucide="${module.icon}"></i><span class="module-node-selected" aria-hidden="true"><i data-lucide="eye"></i>查看中</span><span class="module-node-state"><span class="module-state-dot" aria-hidden="true"></span><span data-module-state>未运行</span></span></span>
    <span class="module-node-name">${module.name}</span><span class="module-node-subject">${module.subject}</span>
  </button>`;
};
const edge = (from: WebModuleId, to: WebModuleId | 'research', direction: 'up' | 'down' | 'left' | 'right', className: string) =>
  `<span class="module-edge ${className}" data-from="${from}" data-to="${to}" data-direction="${direction}" aria-hidden="true"></span>`;

export class ModuleView {
  private root?: HTMLElement;
  private input?: ModuleViewInput;
  private identity = '';
  private selected: WebModuleId = 'M1';
  private selectedPolicy?: string;
  private following = false;
  private scrollTop = 0;

  constructor(private readonly icons: (root: HTMLElement) => void) {}

  update(root?: HTMLElement, input?: ModuleViewInput) {
    if (this.root?.getClientRects().length) this.scrollTop = this.scroller()?.scrollTop ?? 0;
    if (input && this.identity !== input.id) {
      this.selected = 'M1'; this.selectedPolicy = undefined; this.following = false; this.scrollTop = 0; this.identity = input.id;
    }
    if (!root || !input) { this.root = undefined; return; }
    this.input = input;
    this.root = root;
    if (!root.querySelector('.module-layout')) this.mount();
    this.render();
    const scroll = this.scroller();
    if (scroll && root.getClientRects().length) scroll.scrollTop = this.scrollTop;
  }

  private scroller() { return this.root?.closest<HTMLElement>('.detail-panel,.draft-preview'); }

  focusPolicy(id: string) {
    if (!this.root?.getClientRects().length) return;
    const rule = this.input?.modulePlan?.custom.find(rule => rule.id === id);
    if (rule) { this.select(rule.slot, rule.id); return; }
    const node = this.root.querySelector<HTMLButtonElement>(`[data-module-id="${this.selected}"]`);
    node?.focus({ preventScroll: true }); node?.scrollIntoView({ block: 'nearest', behavior: 'instant' });
  }

  private mount() {
    const root = this.root!;
    root.innerHTML = `<header class="module-view-heading"><div><h3><span>研究模块</span><button type="button" class="icon-button module-configure" data-module-configure title="编辑模块方案" aria-label="编辑模块方案"><i data-lucide="sliders-horizontal"></i></button></h3><p data-module-configuration></p></div><span class="module-observation" role="status" aria-atomic="true"></span></header>
      <section class="module-live" aria-label="最近模块活动" hidden>
        <div class="module-live-heading"><span>最近活动</span><time class="mono"></time></div>
        <div class="module-live-controls"><label class="module-follow"><input type="checkbox" data-module-follow aria-controls="module-inspector"><span>实时跟随</span></label><button type="button" class="icon-button" data-module-latest title="定位最近活动" aria-label="定位最近活动" aria-controls="module-inspector"><i data-lucide="locate-fixed"></i></button></div>
        <p class="module-live-event"><strong data-module-live-name></strong><span data-module-live-message></span></p>
      </section>
      <div class="module-layout">
        <div class="module-graph" role="group" aria-label="M3 搜索、M4 上下文、M1 构造、M2 检查组成研究循环，M5 协调，S3 独立验收" aria-describedby="module-graph-note">
          ${node('M5')}${edge('M5', 'research', 'down', 'module-coordination-edge')}
          <div class="module-research"><div class="module-cycle">${node('M3')}${edge('M3', 'M4', 'right', 'module-edge-context')}${node('M4')}${edge('M2', 'M3', 'up', 'module-edge-retry')}<span class="module-cycle-label"><i data-lucide="refresh-cw"></i><span>研究循环</span></span>${edge('M4', 'M1', 'down', 'module-edge-construction')}${node('M2')}${edge('M1', 'M2', 'left', 'module-edge-feedback')}${node('M1')}</div></div>
          <div class="module-acceptance-edge">${edge('M2', 'S3', 'down', '')}<span>候选检查通过后</span></div>${node('S3')}
          <div class="module-legend"><span><i class="module-selected-key"></i>查看中</span><span><i class="module-recent-key"></i>最新记录</span><span><i data-tone="active"></i>进行中</span><span><i data-tone="observed"></i>已有记录</span><span><i data-tone="pending"></i>尚无记录</span></div>
          <p class="module-graph-note" id="module-graph-note">点击模块查看记录 · 连线表示结构关系</p>
          <section class="module-customizations" aria-labelledby="module-customizations-title" hidden><header><h4 id="module-customizations-title">自定义策略</h4><span data-module-custom-count></span></header><ol></ol></section>
        </div>
        <section class="module-inspector" id="module-inspector" aria-labelledby="module-inspector-title" tabindex="-1">
          <header><span class="module-inspector-code mono"></span><h4 id="module-inspector-title"></h4><span class="module-inspector-state" role="status" aria-atomic="true"></span><button type="button" class="icon-button module-policy-add" data-module-policy-add aria-haspopup="dialog" aria-controls="run-settings" hidden><i data-lucide="plus"></i></button><button type="button" class="icon-button module-graph-return" data-module-return title="返回模块图" aria-label="返回模块图"><i data-lucide="arrow-up"></i></button></header>
          <p class="module-output"></p><section class="module-policies" aria-label="当前模块的自定义策略" hidden><div></div></section><dl class="module-facts"></dl>
          <section class="module-workers" hidden aria-labelledby="module-workers-title"><header><h4 id="module-workers-title" title="依据已收到的开始和结束事件，不代表实时请求占用">未结束的 Agent 记录</h4><span data-module-worker-count></span></header><ul></ul></section>
          <p class="module-verification-note" hidden></p>
          <div class="module-history-heading"><h4>最近活动</h4><button type="button" class="icon-button" data-module-destination="events" title="打开活动记录" aria-label="打开活动记录"><i data-lucide="list"></i></button></div>
          <p class="module-retention"></p><ol class="module-events"></ol><p class="module-events-empty"></p>
          <button type="button" class="text-button module-destination" data-module-destination="source"><i data-lucide="file-code-2"></i><span>Lean 源码</span></button>
        </section>
      </div>`;
    root.addEventListener('change', event => {
      const follow = (event.target as Element).closest<HTMLInputElement>('[data-module-follow]');
      if (!follow) return;
      this.following = follow.checked;
      this.render();
    });
    root.addEventListener('click', event => {
      if ((event.target as Element).closest('[data-module-return]')) {
        root.querySelector('.module-graph')!.scrollIntoView({ block: 'start', behavior: 'instant' });
        root.querySelector<HTMLButtonElement>(`[data-module-id="${this.selected}"]`)!.focus({ preventScroll: true });
        return;
      }
      if ((event.target as Element).closest('[data-module-latest]')) {
        const latest = this.input?.run && latestModuleActivity(webModuleSnapshots(this.input.run));
        if (!latest) return;
        this.select(latest.id);
        return;
      }
      const id = (event.target as Element).closest<HTMLElement>('[data-module-id]')?.dataset.moduleId;
      const slot = id ?? (event.target as Element).closest<HTMLElement>('[data-module-slot]')?.dataset.moduleSlot;
      if (!modules.some(module => module.id === slot)) return;
      const policy = (event.target as Element).closest<HTMLElement>('[data-module-custom-id]')?.dataset.moduleCustomId;
      this.select(slot as WebModuleId, policy);
    });
    this.icons(root);
  }

  private select(id: WebModuleId, policy?: string) {
    this.following = false;
    this.selected = id; this.selectedPolicy = policy;
    this.render();
    const rule = policy && Array.from(this.root!.querySelectorAll<HTMLDetailsElement>('[data-module-policy-id]'))
      .find(row => row.dataset.modulePolicyId === policy);
    if (rule) {
      rule.open = true;
      rule.querySelector('summary')!.focus({ preventScroll: true });
      rule.scrollIntoView({ block: 'nearest', behavior: 'instant' });
      return;
    }
    const inspector = this.root!.querySelector<HTMLElement>('.module-inspector')!;
    if (inspector.getBoundingClientRect().top >= this.root!.querySelector('.module-graph')!.getBoundingClientRect().bottom) {
      inspector.focus({ preventScroll: true });
      inspector.scrollIntoView({ block: 'start', behavior: 'instant' });
    }
  }

  private render() {
    const root = this.root!, input = this.input!, run = input.run;
    const plan = input.modulePlan ?? defaultResearchModulePlan();
    const selectedRule = plan.custom.find(rule => rule.id === this.selectedPolicy);
    if (selectedRule) this.selected = selectedRule.slot;
    else this.selectedPolicy = undefined;
    const snapshots = run ? webModuleSnapshots(run) : {};
    const latest = latestModuleActivity(snapshots);
    const live = Boolean(run && (run.status === 'running' || run.status === 'queued'));
    if (!live) this.following = false;
    if (this.following && input.connected && latest) { this.selected = latest.id; this.selectedPolicy = undefined; }
    const activity = root.querySelector<HTMLElement>('.module-live')!;
    activity.hidden = !run;
    const follow = activity.querySelector<HTMLInputElement>('[data-module-follow]')!;
    follow.checked = this.following;
    follow.disabled = !live;
    activity.querySelector<HTMLButtonElement>('[data-module-latest]')!.disabled = !latest;
    const latestTime = activity.querySelector('time')!;
    latestTime.dateTime = latest?.event.at ?? '';
    text(latestTime, latest ? timestamp(latest.event.at) : '');
    text(activity.querySelector('[data-module-live-name]')!, latest ? `${latest.id} · ${modules.find(module => module.id === latest.id)!.name}` : '');
    text(activity.querySelector('[data-module-live-message]')!, latest?.event.message ?? '等待模块活动');
    activity.querySelector<HTMLElement>('.module-live-event')!.title = latest?.event.message ?? '';
    const configuredWorkers = Number.isSafeInteger(input.workers) && input.workers > 0 ? input.workers : '未设置';
    text(root.querySelector('[data-module-configuration]')!, `5 个研究模块 · ${configuredWorkers} 个 Agent · ${input.coordination === 'cooperative' ? '任务协作' : '独立并行'}`);
    root.querySelector<HTMLButtonElement>('[data-module-configure]')!.hidden = Boolean(run);
    root.dataset.stale = String(!input.connected);
    text(root.querySelector('.module-observation')!, !input.connected ? '连接中断 · 最近状态' : !run ? '未提交'
      : `${runProgress(run).phaseLabel} · ${timestamp(run.updatedAt)}`);
    for (const module of modules) {
      const button = root.querySelector<HTMLButtonElement>(`[data-module-id="${module.id}"]`)!;
      const value = moduleState(module.id, run, snapshots[module.id]);
      const rules = plan.custom.filter(rule => rule.enabled && rule.slot === module.id
        && (rule.slot !== 'M5' || input.coordination === 'cooperative' && input.workers > 1));
      button.dataset.tone = value.tone;
      button.dataset.recent = String(latest?.id === module.id);
      button.setAttribute('aria-pressed', String(this.selected === module.id));
      button.setAttribute('aria-current', String(latest?.id === module.id));
      button.title = `${module.name} · ${value.label}${latest?.id === module.id ? ' · 最新模块记录' : ''}${rules.length ? ` · ${rules.map(rule => rule.name).join('、')}` : ''}`;
      text(button.querySelector('.module-node-subject')!, rules.length ? `${rules.length} 个自定义策略` : module.subject);
      text(button.querySelector('[data-module-state]')!, value.label);
    }
    for (const connector of root.querySelectorAll<HTMLElement>('.module-edge'))
      connector.dataset.selected = String(connector.dataset.from === this.selected || connector.dataset.to === this.selected);
    const module = modules.find(module => module.id === this.selected)!, snapshot = snapshots[this.selected];
    const value = moduleState(this.selected, run, snapshot);
    const inspector = root.querySelector<HTMLElement>('.module-inspector')!;
    inspector.dataset.module = this.selected; inspector.dataset.tone = value.tone;
    text(inspector.querySelector('.module-inspector-code')!, module.id);
    text(inspector.querySelector('h4')!, module.name);
    text(inspector.querySelector('.module-inspector-state')!, value.label);
    const add = inspector.querySelector<HTMLButtonElement>('[data-module-policy-add]')!;
    add.hidden = Boolean(run) || !['M1', 'M3', 'M4', 'M5'].includes(this.selected);
    add.dataset.modulePolicyAdd = this.selected; add.disabled = plan.custom.length >= 8;
    add.title = add.disabled ? '最多保存 8 个自定义策略' : `新增 ${this.selected} 策略`;
    add.setAttribute('aria-label', add.title);
    const outputs: Record<WebModuleId, string> = { M1: '输出：候选源码与研究进展', M2: '输出：候选检查结果与 Lean 反馈', M3: '输出：下一步研究动作', M4: '输出：当前尝试的研究上下文', M5: '输出：任务分配、审阅与集成记录', S3: '验收范围：固定的完整原题' };
    text(inspector.querySelector('.module-output')!, outputs[this.selected]);
    const note = inspector.querySelector<HTMLElement>('.module-verification-note')!;
    note.hidden = !['M1', 'M2', 'S3'].includes(this.selected);
    text(note, this.selected === 'S3' ? '完整原题通过独立 Lean 验收，才记为验收通过。' : '候选、局部任务和条件性检查结果均不代表完整原题验收通过。');
    const details = snapshot?.lastEvent.details;
    const facts: Array<[string, string]> = [['状态', value.label], ['活动事件', String(snapshot?.eventCount ?? 0)]];
    if (this.selected === 'M1') facts.push(['模型', input.model || '未设置']);
    if (this.selected === 'M2' || this.selected === 'S3') facts.push(['证明环境', input.environment]);
    if (this.selected === 'M3' && details?.operation) facts.push(['最近决策', operations[details.operation]]);
    if (this.selected === 'M3') facts.push(['调度策略', `${schedulers[plan.scheduler] ?? plan.scheduler}${input.coordination !== 'cooperative' || input.workers <= 1 ? ' · 多 Agent 协作时生效' : ''}`]);
    if (this.selected === 'M4') facts.push(['上下文范围', plan.context === 'essential' ? '必要原题、接口与检查反馈' : '完整研究证据']);
    if (this.selected === 'M4' && details?.usedBytes !== undefined)
      facts.push(['上下文大小', `${bytes(details.usedBytes)}${details.maxBytes !== undefined ? ` / ${bytes(details.maxBytes)}` : ''}`]);
    if (this.selected === 'M5') facts.push(['运行模式', input.coordination === 'cooperative' ? '任务协作' : '独立并行'], ['Agent 配置', String(configuredWorkers)]);
    if (details?.workerId) facts.push(['最近 Agent', details.workerId]);
    if (details?.turn !== undefined) facts.push(['最近轮次', String(details.turn)]);
    if (snapshot) facts.push(['最近记录', timestamp(snapshot.lastEvent.at)]);
    this.renderFacts(facts);
    this.renderCustomizations(plan.custom);
    this.renderPolicies(plan.custom.filter(rule => rule.slot === this.selected));
    this.renderWorkers(value.tone === 'active' ? snapshot?.activeWorkers ?? [] : []);
    const events = run?.events.filter(event => webEventModule(event.type) === this.selected).slice(-6).reverse() ?? [];
    this.renderEvents(events);
    const cumulative = Boolean(run?.modules?.[this.selected]);
    text(inspector.querySelector('.module-retention')!, events.length
      ? `显示最近 ${events.length} 条${snapshot && snapshot.eventCount > events.length ? ` · ${cumulative ? '累计' : '保留窗口内'} ${snapshot.eventCount} 条` : ''}`
      : snapshot ? `累计 ${snapshot.eventCount} 条 · 较早活动已移出保留范围` : '');
    const empty = inspector.querySelector<HTMLElement>('.module-events-empty')!;
    empty.hidden = Boolean(events.length);
    text(empty, run ? snapshot ? snapshot.lastEvent.message : '该模块暂无活动记录' : '提交后记录真实模块活动');
    inspector.querySelector<HTMLButtonElement>('[data-module-destination="events"]')!.hidden = !run;
    const destination = inspector.querySelector<HTMLButtonElement>('.module-destination')!;
    destination.dataset.moduleDestination = this.selected === 'S3' && run ? 'report' : 'source';
    text(destination.querySelector('span')!, this.selected === 'S3' && run ? '验收报告' : 'Lean 源码');
  }

  private renderCustomizations(rules: CustomResearchModule[]) {
    const section = this.root!.querySelector<HTMLElement>('.module-customizations')!;
    section.hidden = !rules.length;
    text(section.querySelector('[data-module-custom-count]')!, `${rules.filter(rule => rule.enabled).length} / ${rules.length} 已启用`);
    const target = section.querySelector('ol')!;
    const rows = new Map(Array.from(target.querySelectorAll<HTMLElement>('[data-module-custom-id]')).map(row => [row.dataset.moduleCustomId!, row]));
    for (const [id, row] of rows) if (!rules.some(rule => rule.id === id)) row.closest('li')!.remove();
    const applications = this.input!.run ? webCustomModuleSnapshots(this.input!.run) : {};
    let cursor = target.firstElementChild;
    for (const rule of rules) {
      let button = rows.get(rule.id);
      if (!button) {
        const row = document.createElement('li');
        row.className = 'module-customization-row';
        row.innerHTML = '<label class="module-custom-toggle"><input type="checkbox" data-module-custom-enabled></label><button type="button" class="module-customization" aria-controls="module-inspector"><span class="module-custom-slot mono"></span><span class="module-custom-name"></span><span class="module-custom-mode"></span><span data-module-custom-state></span><i data-lucide="arrow-up-right"></i></button>';
        button = row.querySelector('button')!; button.dataset.moduleCustomId = rule.id;
        this.icons(row);
      }
      const row = button.closest('li')!;
      row.dataset.selected = String(this.selectedPolicy === rule.id);
      const toggle = row.querySelector<HTMLInputElement>('[data-module-custom-enabled]')!;
      toggle.dataset.moduleCustomEnabled = rule.id;
      if (toggle.checked !== rule.enabled) toggle.checked = rule.enabled;
      toggle.disabled = Boolean(this.input!.run) || this.input!.editable === false;
      toggle.setAttribute('aria-label', `启用${rule.name || '未命名策略'}`);
      const label = toggle.closest<HTMLLabelElement>('label')!;
      label.hidden = Boolean(this.input!.run);
      label.title = `${rule.enabled ? '停用' : '启用'}${rule.name || '未命名策略'}`;
      const state = customModuleState(rule, this.input!, applications[rule.id]);
      button.dataset.moduleSlot = rule.slot;
      button.dataset.enabled = String(rule.enabled);
      button.dataset.appliedCount = String(applications[rule.id]?.eventCount ?? 0);
      button.setAttribute('aria-label', `${rule.name || '未命名策略'} · ${rule.slot} · ${state}`);
      button.title = rule.name || '未命名策略';
      if (this.selectedPolicy === rule.id) button.setAttribute('aria-current', 'true');
      else button.removeAttribute('aria-current');
      text(button.querySelector('.module-custom-slot')!, rule.slot);
      text(button.querySelector('.module-custom-name')!, rule.name || '未命名策略');
      text(button.querySelector('.module-custom-mode')!, rule.mode === 'replace' ? '替换建议' : '补充建议');
      text(button.querySelector('[data-module-custom-state]')!, state);
      if (row !== cursor) target.insertBefore(row, cursor);
      cursor = row.nextElementSibling;
    }
  }

  private renderPolicies(rules: CustomResearchModule[]) {
    const section = this.root!.querySelector<HTMLElement>('.module-policies')!;
    section.hidden = !rules.length;
    const target = section.querySelector('div')!;
    const rows = new Map(Array.from(target.querySelectorAll<HTMLElement>('[data-module-policy-id]')).map(row => [row.dataset.modulePolicyId!, row]));
    for (const [id, row] of rows) if (!rules.some(rule => rule.id === id)) row.remove();
    const applications = this.input!.run ? webCustomModuleSnapshots(this.input!.run) : {};
    let cursor = target.firstElementChild;
    for (const rule of rules) {
      let row = rows.get(rule.id);
      if (!row) {
        row = document.createElement('details'); row.dataset.modulePolicyId = rule.id;
        row.innerHTML = '<summary><span class="module-policy-name"></span><span class="module-policy-state"></span><i data-lucide="chevron-down"></i></summary><div class="module-policy-tools"><p class="module-policy-mode"></p><button type="button" class="icon-button module-policy-edit" aria-haspopup="dialog" aria-controls="run-settings" hidden><i data-lucide="square-pen"></i></button></div><p class="module-policy-instructions"></p>';
        this.icons(row);
      }
      row.dataset.enabled = String(rule.enabled);
      row.dataset.selected = String(this.selectedPolicy === rule.id);
      const edit = row.querySelector<HTMLButtonElement>('.module-policy-edit')!;
      edit.dataset.modulePolicyEdit = rule.id; edit.hidden = Boolean(this.input!.run);
      edit.title = `编辑${rule.name || '未命名策略'}`; edit.setAttribute('aria-label', edit.title);
      text(row.querySelector('.module-policy-name')!, rule.name || '未命名策略');
      text(row.querySelector('.module-policy-state')!, customModuleState(rule, this.input!, applications[rule.id]));
      text(row.querySelector('.module-policy-mode')!, rule.mode === 'replace' ? '替换默认建议' : '补充默认建议');
      text(row.querySelector('.module-policy-instructions')!, rule.instructions || '规则未填写');
      if (row !== cursor) target.insertBefore(row, cursor);
      cursor = row.nextElementSibling;
    }
  }

  private renderWorkers(workers: string[]) {
    const section = this.root!.querySelector<HTMLElement>('.module-workers')!;
    section.hidden = !workers.length;
    text(section.querySelector('[data-module-worker-count]')!, String(workers.length));
    const target = section.querySelector('ul')!;
    const rows = new Map(Array.from(target.querySelectorAll<HTMLElement>('[data-worker-id]')).map(row => [row.dataset.workerId!, row]));
    for (const [id, row] of rows) if (!workers.includes(id)) row.remove();
    let cursor = target.firstElementChild;
    for (const id of workers) {
      let row = rows.get(id);
      if (!row) { row = document.createElement('li'); row.dataset.workerId = id; row.innerHTML = '<span aria-hidden="true"></span><code></code>'; }
      text(row.querySelector('code')!, id);
      if (row !== cursor) target.insertBefore(row, cursor);
      cursor = row.nextElementSibling;
    }
  }

  private renderFacts(facts: Array<[string, string]>) {
    const target = this.root!.querySelector('.module-facts')!;
    const rows = new Map(Array.from(target.children).map(row => [row.querySelector('dt')!.textContent, row]));
    for (const [label] of rows) if (!facts.some(fact => fact[0] === label)) rows.get(label)!.remove();
    let cursor = target.firstElementChild;
    for (const [label, value] of facts) {
      let row = rows.get(label);
      if (!row) { row = document.createElement('div'); row.innerHTML = '<dt></dt><dd></dd>'; }
      text(row.querySelector('dt')!, label); text(row.querySelector('dd')!, value);
      if (row !== cursor) target.insertBefore(row, cursor);
      cursor = row.nextElementSibling;
    }
  }

  private renderEvents(events: WebEvent[]) {
    const target = this.root!.querySelector('.module-events')!;
    const rows = new Map(Array.from(target.querySelectorAll<HTMLElement>('[data-sequence]')).map(row => [Number(row.dataset.sequence), row]));
    for (const [sequence, row] of rows) if (!events.some(event => event.sequence === sequence)) row.remove();
    let cursor = target.firstElementChild;
    for (const event of events) {
      let row = rows.get(event.sequence);
      if (!row) {
        row = document.createElement('li'); row.dataset.sequence = String(event.sequence);
        row.innerHTML = '<time class="mono"></time><p></p>';
      }
      const time = row.querySelector('time')!;
      time.dateTime = event.at; text(time, timestamp(event.at));
      text(row.querySelector('p')!, event.message);
      if (row !== cursor) target.insertBefore(row, cursor);
      cursor = row.nextElementSibling;
    }
  }
}
