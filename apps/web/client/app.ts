import {
  createIcons, ArrowRight, ArrowUpRight, Check, CheckCheck, ChevronDown, ChevronUp, CircleAlert, CircleCheck, Clock3, Copy, CopyPlus, Cpu,
  Download, Eye, EyeOff, FileCode2, FileJson2, FlaskConical, GitBranch, List, Maximize2, Network,
  Play, Plus, RefreshCw, RotateCcw, Search, SlidersHorizontal, Square, Trash2, TriangleAlert, Upload, X,
} from 'lucide';
import type { WebCoordination, WebEffort, WebEnvironment, WebRun, WebRunInput, WebSession } from '../shared';
import { formatDuration, isAcceptedRun, resultDescription, runProgress } from '../presentation';
import { summarizeReport, type ReportCheck, type ReportTarget } from '../report';
import { filterRuns, type RunFilter } from './history';
import { readLeanFile } from './sourceFile';
import { decodeTaskDraft, encodeTaskDraft, readTaskDraftFile, taskDraftStorageKey, type TaskDraft } from './draft';
import { compareSources, type SourceComparison, type SourceDiffRow } from './sourceDiff';

const iconSet = { ArrowRight, ArrowUpRight, Check, CheckCheck, ChevronDown, ChevronUp, CircleAlert, CircleCheck, Clock3, Copy, CopyPlus, Cpu,
  Download, Eye, EyeOff, FileCode2, FileJson2, FlaskConical, GitBranch, List, Maximize2, Network,
  Play, Plus, RefreshCw, RotateCcw, Search, SlidersHorizontal, Square, Trash2, TriangleAlert, Upload, X };
const icons = () => createIcons({ icons: iconSet, attrs: { 'aria-hidden': 'true' } });
const icon = (name: string) => `<i data-lucide="${name}"></i>`;
const html = (value: unknown) => String(value ?? '').replace(/[&<>"']/g, character => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
}[character]!));
function element<T extends HTMLElement = HTMLElement>(selector: string): T {
  const result = document.querySelector<T>(selector);
  if (!result) throw new Error(`Missing workbench element: ${selector}`);
  return result;
}
const field = (id: string) => element<HTMLInputElement | HTMLSelectElement | HTMLTextAreaElement>(`#${id}`);
const activeRun = (run: WebRun) => run.status === 'queued' || run.status === 'running';
const passed = isAcceptedRun;
const timestamp = (value: string, timeOnly = false) => {
  const date = new Date(value);
  if (!Number.isFinite(date.getTime())) return value;
  return new Intl.DateTimeFormat('zh-CN', timeOnly
    ? { hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false }
    : { month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', hour12: false }).format(date);
};
const byteSize = (text: string) => new TextEncoder().encode(text).length;
const byteLabel = (bytes: number) => bytes >= 1024 ? `${(bytes / 1024).toFixed(1)} KB` : `${bytes} B`;
type DetailTab = 'overview' | 'source' | 'report' | 'events';
const state = {
  session: undefined as WebSession | undefined,
  runs: [] as WebRun[], selectedId: '', selectedRun: undefined as WebRun | undefined,
  query: '', filter: 'all' as RunFilter,
  tab: 'overview' as DetailTab, sourceView: 'proof' as 'proof' | 'input' | 'diff', submitting: false, cancelling: new Set<string>(),
  foldUnchanged: true, diffChange: 0,
  reportMode: 'summary' as 'summary' | 'json', deleting: new Set<string>(),
  detailError: '', listGeneration: 0,
  listSignature: '', detailSignature: '', panelSignature: '',
  connected: false, refreshing: false, connectionEpoch: 0,
};
let pollTimer: ReturnType<typeof setTimeout> | undefined;
let toastTimer: ReturnType<typeof setTimeout> | undefined;
let clockTimer: ReturnType<typeof setInterval> | undefined;
let connectionRequest: Promise<void> | undefined;
let readController = new AbortController();
let pageActive = true;
let sourceRevision = 0;
let editorRevision = 0;
let deletionTarget: { id: string; title: string; csrfToken: string } | undefined;
let draftReady = false;
let draftDirty = false;
let draftRevision = 0;
let draftTimer: ReturnType<typeof setTimeout> | undefined;
let taskImportSequence = 0;
let pendingImport: { draft: TaskDraft; revision: number } | undefined;
let sourceComparison: { runId: string; before: string; after: string; folded: boolean; result: SourceComparison } | undefined;
let draftPreviewSignature = '';

class ApiError extends Error {
  constructor(message: string, readonly status: number) { super(message); }
}
async function api<T>(url: string, init: RequestInit = {}): Promise<T> {
  const timeout = new AbortController();
  const timer = setTimeout(() => timeout.abort(new Error('请求超时，请重新连接')), 15_000);
  const signals = [timeout.signal];
  if (!init.method || init.method === 'GET') signals.push(readController.signal);
  if (init.signal) signals.push(init.signal);
  try {
    const response = await fetch(url, { ...init, credentials: 'same-origin', cache: 'no-store', signal: AbortSignal.any(signals),
      headers: { Accept: 'application/json', ...(init.body ? { 'Content-Type': 'application/json' } : {}),
        ...(init.method && init.method !== 'GET' ? { 'X-CSRF-Token': state.session?.csrfToken ?? '' } : {}), ...init.headers } });
    const payload: unknown = await response.json().catch(error => {
      if (timeout.signal.aborted) throw timeout.signal.reason;
      if (!response.ok) return undefined;
      throw error;
    });
    if (!response.ok) {
      const message = payload && typeof payload === 'object' && 'error' in payload && typeof payload.error === 'string'
        ? payload.error : `请求失败 (${response.status})`;
      throw new ApiError(message, response.status);
    }
    if (payload === undefined) throw new Error('服务器返回了无法读取的响应');
    return payload as T;
  } catch (error) {
    if (timeout.signal.aborted) throw timeout.signal.reason;
    throw error;
  } finally {
    clearTimeout(timer);
  }
}
const message = (error: unknown) => error instanceof Error ? error.message : '请求失败，请重试';
function toast(text: string) {
  const target = element('#toast');
  target.textContent = text; target.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { target.hidden = true; }, 3000);
}
function setGlobalNotice(text: string) {
  element('#global-notice-text').textContent = text;
  element('#global-notice').hidden = !text;
}
function setMobileView(view: 'compose' | 'runs', focus = false) {
  document.body.dataset.mobileView = view;
  document.querySelectorAll<HTMLButtonElement>('button[data-mobile-view]').forEach(button => {
    const selected = button.dataset.mobileView === view;
    button.setAttribute('aria-selected', String(selected)); button.tabIndex = selected ? 0 : -1;
    if (selected && focus) button.focus();
  });
  if (view === 'runs') {
    renderDraftPreview();
    const list = element('#run-list');
    const selected = list.querySelector<HTMLElement>('.run-row.selected');
    if (selected && list.scrollWidth > list.clientWidth) {
      const bounds = list.getBoundingClientRect(), row = selected.getBoundingClientRect();
      if (row.left < bounds.left) list.scrollLeft += row.left - bounds.left;
      else if (row.right > bounds.right) list.scrollLeft += row.right - bounds.right;
    }
  }
}
function providerAddress() {
  element('#provider-address').textContent = state.session?.providers.find(provider => provider.id === field('provider').value)?.baseUrl ?? '';
}
const environmentInfo = (id: WebEnvironment | string) => state.session?.environments.find(environment => environment.id === id);
const environmentName = (id: WebEnvironment | string) => environmentInfo(id)?.name ?? (id === 'mathlib' ? 'Mathlib' : 'Lean 标准库');
const leanVersion = (toolchain: string) => toolchain.replace(/^leanprover\/lean4:/, '');
function updateEnvironment() {
  const environment = environmentInfo(field('environment').value);
  element('#lean-scope').textContent = environment ? leanVersion(environment.toolchain) : '';
  const details = element('#environment-details');
  details.textContent = environment
    ? `Lean ${leanVersion(environment.toolchain)}${environment.mathlibRevision ? ` · Mathlib ${environment.mathlibRevision.slice(0, 8)}` : ' · 标准库'}`
    : '请选择证明环境';
  details.title = environment
    ? `${environment.description} · Lean ${leanVersion(environment.toolchain)}${environment.mathlibRevision ? ` · Mathlib ${environment.mathlibRevision}` : ''}`
    : '请选择证明环境';
  details.setAttribute('aria-label', details.title);
}
function renderTemplates(preferred = '', useFirst = false) {
  const templates = state.session?.templates.filter(template => template.environment === field('environment').value) ?? [];
  field('template').innerHTML = templates.map(template => `<option value="${html(template.id)}">${html(template.name)}</option>`).join('') + '<option value="">自定义 Lean</option>';
  field('template').value = templates.some(template => template.id === preferred) ? preferred : useFirst ? templates[0]?.id ?? '' : '';
}
function updateCounts() {
  for (const [id, limit] of [['source', state.session?.limits.maxSourceBytes], ['task', state.session?.limits.maxTaskBytes]] as const) {
    const count = byteSize(field(id).value);
    const target = element(`#${id}-count`);
    target.textContent = limit ? `${byteLabel(count)} / ${byteLabel(limit)}` : byteLabel(count);
    target.classList.toggle('over-limit', Boolean(limit && count > limit));
  }
  element('#source-lines').textContent = `${field('source').value.split(/\r\n|\r|\n/).length} 行`;
}
function sourceChanged() {
  sourceRevision++;
  element('#source-error').hidden = true;
  updateCounts();
  draftChanged();
}
function captureDraft(): TaskDraft {
  return { providerId: field('provider').value, model: field('model').value,
    effort: field('effort').value as WebEffort, environment: field('environment').value as WebEnvironment,
    source: field('source').value, task: field('task').value, templateId: field('template').value,
    maxTurns: field('max-turns').value, maxRunSeconds: field('max-seconds').value, workers: field('workers').value,
    coordination: element<HTMLInputElement>('input[name="coordination"]:checked').value as WebCoordination };
}
function setDraftStatus(text: string, warning = false) {
  element('#draft-status').textContent = text;
  element('#draft-status').classList.toggle('warning', warning);
}
function draftChanged(persist = true) {
  draftRevision++;
  renderImportState();
  renderDraftPreview();
  if (!draftReady || !persist) return;
  draftDirty = true;
  setDraftStatus('草稿待保存');
  clearTimeout(draftTimer);
  draftTimer = setTimeout(saveDraft, 250);
}
function saveDraft() {
  clearTimeout(draftTimer);
  if (!draftReady || !draftDirty) return;
  try {
    sessionStorage.setItem(taskDraftStorageKey, encodeTaskDraft(captureDraft()));
    draftDirty = false;
    setDraftStatus('草稿已保存');
  } catch {
    // Avoid restoring an older draft after the latest edits could not be saved.
    try { sessionStorage.removeItem(taskDraftStorageKey); } catch { /* Storage can be unavailable. */ }
    setDraftStatus('草稿未保存', true);
  }
}
function applyTaskDraft(draft: TaskDraft) {
  field('provider').value = state.session?.providers.some(provider => provider.id === draft.providerId) ? draft.providerId : '';
  field('environment').value = draft.environment;
  renderTemplates();
  for (const [id, value] of Object.entries({ model: draft.model, effort: draft.effort, source: draft.source, task: draft.task,
    'max-turns': draft.maxTurns, 'max-seconds': draft.maxRunSeconds, workers: draft.workers })) field(id).value = value;
  const template = state.session?.templates.find(template => template.id === draft.templateId
    && template.environment === draft.environment && template.source === field('source').value && template.task === field('task').value);
  field('template').value = template?.id ?? '';
  element<HTMLInputElement>(`input[name="coordination"][value="${draft.coordination}"]`).checked = true;
  field('api-key').value = '';
  element<HTMLInputElement>('#api-key').type = 'password';
  updateKeyToggle(); providerAddress(); updateEnvironment(); sourceChanged();
  element('#form-error').hidden = true;
  element('#draft-error').hidden = true;
}
function restoreDraft() {
  let stored: string | null;
  try { stored = sessionStorage.getItem(taskDraftStorageKey); }
  catch { setDraftStatus('草稿保存不可用', true); return; }
  if (!stored) return;
  try {
    applyTaskDraft(decodeTaskDraft(JSON.parse(stored)));
    setDraftStatus('已恢复草稿');
  } catch {
    try { sessionStorage.removeItem(taskDraftStorageKey); } catch { /* Storage can be unavailable. */ }
    setDraftStatus('草稿未恢复', true);
  }
}
function renderImportState() {
  if (!pendingImport) return;
  const notice = pendingImport.revision !== draftRevision ? '草稿已变化，请重新选择文件。'
    : state.submitting ? '正在提交任务，请稍后再载入。' : '';
  element('#import-notice').textContent = notice;
  element('#import-notice').hidden = !notice;
  element<HTMLButtonElement>('#confirm-import').disabled = Boolean(notice) || !state.session;
}
async function importTaskFile(file: File) {
  if (!state.session || state.submitting) return;
  const sequence = ++taskImportSequence, revision = draftRevision;
  element('#draft-error').hidden = true;
  try {
    const draft = await readTaskDraftFile(file);
    if (sequence !== taskImportSequence) return;
    if (revision !== draftRevision || state.submitting) { toast('草稿已变化，未导入文件'); return; }
    pendingImport = { draft, revision };
    element('#import-filename').textContent = file.name;
    const provider = state.session?.providers.find(provider => provider.id === draft.providerId);
    element('#import-facts').innerHTML = [fact('证明环境', environmentName(draft.environment)),
      fact('服务商', provider?.name ?? `${draft.providerId || '未选择'} · 当前不可用`), fact('模型', draft.model || '未填写', true),
      fact('推理强度', draft.effort), fact('轮次上限', draft.maxTurns || '未填写'),
      fact('解题预算 / 秒', draft.maxRunSeconds || '未填写'), fact('Agent 数量', draft.workers || '未填写'),
      fact('协作模式', draft.coordination === 'cooperative' ? '任务协作' : '独立并行')].join('');
    element('#import-task-preview').textContent = draft.task || '未填写';
    element('#import-source-preview').textContent = draft.source || '未填写';
    renderImportState();
    const dialog = element<HTMLDialogElement>('#import-task-dialog');
    if (!dialog.open) dialog.showModal();
    element('#cancel-import').focus();
  } catch (error) {
    if (sequence !== taskImportSequence || revision !== draftRevision) return;
    element('#draft-error').textContent = message(error);
    element('#draft-error').hidden = false;
  }
}
function applyTemplate(id: string) {
  const template = state.session?.templates.find(item => item.id === id && item.environment === field('environment').value);
  if (template) { field('source').value = template.source; field('task').value = template.task; }
  sourceChanged();
}
function resetForm() {
  const session = state.session;
  if (!session || state.submitting) return;
  const wasReady = draftReady;
  draftReady = false;
  clearTimeout(draftTimer); draftDirty = false;
  element<HTMLFormElement>('#run-form').reset();
  field('api-key').value = '';
  element<HTMLInputElement>('#api-key').type = 'password';
  updateKeyToggle();
  for (const [id, value] of Object.entries({ model: session.defaults.model, effort: session.defaults.effort,
    'max-turns': session.defaults.maxTurns, 'max-seconds': session.defaults.maxRunSeconds, workers: session.defaults.workers })) field(id).value = String(value);
  element<HTMLInputElement>(`input[name="coordination"][value="${session.defaults.coordination}"]`).checked = true;
  field('provider').value = session.providers[0]?.id ?? '';
  field('environment').value = session.defaults.environment;
  renderTemplates('', true);
  field('source').value = ''; field('task').value = '';
  applyTemplate(field('template').value); providerAddress(); updateEnvironment();
  element('#form-error').hidden = true;
  element('#draft-error').hidden = true;
  draftReady = wasReady;
  if (wasReady) {
    try { sessionStorage.removeItem(taskDraftStorageKey); setDraftStatus('草稿已重置'); }
    catch { setDraftStatus('草稿保存不可用', true); }
  }
}
function setCustomSource(source: string) {
  if (field('template').value) field('task').value = '保留原题声明，补全 Lean 证明并通过独立验收。';
  field('template').value = '';
  field('source').value = source;
  sourceChanged();
}
function updateEditorCount() {
  const source = field('expanded-source').value;
  const size = byteSize(source), limit = state.session?.limits.maxSourceBytes;
  const target = element('#editor-count');
  target.textContent = `${source.split(/\r\n|\r|\n/).length} 行 · ${byteLabel(size)}${limit ? ` / ${byteLabel(limit)}` : ''}`;
  target.classList.toggle('over-limit', Boolean(limit && size > limit));
}
function openEditor() {
  if (!state.session || state.submitting) return;
  editorRevision = sourceRevision;
  field('expanded-source').value = field('source').value;
  const environment = environmentInfo(field('environment').value);
  element('#editor-environment').textContent = environment ? `${environment.name} · ${leanVersion(environment.toolchain)}` : '';
  element('#editor-error').hidden = true;
  updateEditorCount();
  element<HTMLDialogElement>('#source-editor').showModal();
  field('expanded-source').focus();
}
function applyEditor() {
  const source = field('expanded-source').value;
  const error = !source.trim() ? 'Lean 源码不能为空'
    : source.includes('\0') ? '源码包含无效字符'
      : byteSize(source) > (state.session?.limits.maxSourceBytes ?? 0) ? 'Lean 源码超出允许大小'
        : editorRevision !== sourceRevision ? '原始草稿已变化，请重新打开编辑器后修改' : '';
  element('#editor-error').textContent = error;
  element('#editor-error').hidden = !error;
  if (error) return;
  if (source !== field('source').value) setCustomSource(source);
  element<HTMLDialogElement>('#source-editor').close();
}
function updateKeyToggle() {
  const visible = element<HTMLInputElement>('#api-key').type === 'text';
  const button = element('#toggle-key');
  button.setAttribute('aria-label', visible ? '隐藏 API Key' : '显示 API Key');
  button.setAttribute('title', visible ? '隐藏 API Key' : '显示 API Key');
  button.setAttribute('aria-pressed', String(visible));
  button.innerHTML = icon(visible ? 'eye-off' : 'eye');
  icons();
}
function renderRuntime() {
  const session = state.session;
  const ready = Boolean(state.connected && session?.runtime.ready && session.providers.length);
  const connection = element('#connection-status');
  connection.className = `connection-status ${ready ? 'ready' : 'offline'}`;
  connection.innerHTML = `<span class="status-dot"></span>${!state.connected ? connectionRequest ? '连接中' : '连接中断' : ready ? '环境就绪' : '环境未就绪'}`;
  element('#runtime-note').textContent = !state.connected ? '连接恢复后可提交' : session
    ? !session.providers.length ? '未配置可用服务商' : session.runtime.message || (ready ? '环境就绪' : '环境未就绪')
    : '等待连接';
  element<HTMLButtonElement>('#submit-run').disabled = !ready || state.submitting;
  element<HTMLButtonElement>('#submit-run').innerHTML = `${state.submitting ? '<span class="spinner"></span>' : icon('play')}<span>${state.submitting ? '正在提交' : '开始研究'}</span>`;
  element<HTMLFieldSetElement>('#form-fields').disabled = !session || state.submitting;
  element<HTMLButtonElement>('#reset-form').disabled = !session || state.submitting;
  element<HTMLButtonElement>('#import-task').disabled = !session || state.submitting;
  element<HTMLButtonElement>('#export-draft').disabled = !session || state.submitting;
  renderImportState();
  renderDeleteState();
  icons();
}
function status(run: WebRun) {
  if (passed(run)) return { label: '完整原题通过', tone: 'passed', symbol: 'circle-check' };
  if (run.status === 'queued') return { label: '排队中', tone: '', symbol: 'clock-3' };
  if (run.status === 'running') return { label: runProgress(run).phaseLabel, tone: 'running', symbol: 'refresh-cw' };
  if (run.status === 'cancelled') return { label: '已取消', tone: '', symbol: 'square' };
  if (run.status === 'error') return { label: '运行错误', tone: 'failed', symbol: 'circle-alert' };
  if (['evaluated_failed', 'evaluated_rejected'].includes(run.result?.status ?? '')) return { label: '验收未通过', tone: 'failed', symbol: 'circle-alert' };
  return { label: '运行结束', tone: 'warning', symbol: 'clock-3' };
}
const badge = (run: WebRun) => { const value = status(run); return `<span class="badge ${value.tone}">${icon(value.symbol)}${value.label}</span>`; };
function renderRunList(force = false) {
  const runs = visibleRuns();
  const filtered = Boolean(state.query.trim() || state.filter !== 'all');
  const signature = JSON.stringify([state.selectedId, state.query, state.filter, runs.map(run => [run.id, run.title, run.status, run.model, run.environment, run.updatedAt, run.result?.status])]);
  element('#run-count').textContent = filtered ? `${runs.length}/${state.runs.length}` : String(state.runs.length);
  element('#mobile-run-count').textContent = String(state.runs.length);
  element('#clear-run-search').hidden = !state.query;
  if (!force && signature === state.listSignature) return;
  state.listSignature = signature;
  const focused = document.activeElement instanceof HTMLElement ? document.activeElement.dataset.runId : undefined;
  element('#run-list').innerHTML = runs.length ? runs.map(run => `
    <div role="listitem"><button type="button" class="run-row ${run.id === state.selectedId ? 'selected' : ''}" data-run-id="${html(run.id)}" aria-pressed="${run.id === state.selectedId}" title="${html(run.title)}">
      <span class="run-row-title">${html(run.title)}</span><span class="run-row-meta"><span class="run-row-model">${html(run.model)}</span><span class="run-environment">${html(environmentName(run.environment))}</span></span>
      <span class="run-row-bottom">${badge(run)}<time datetime="${html(run.createdAt)}">${html(timestamp(run.createdAt))}</time></span>
    </button></div>`).join('') : `<div class="empty-state compact" role="status">${icon(filtered ? 'search' : 'clock-3')}<p>${filtered ? '没有匹配的运行' : '暂无运行记录'}</p>${filtered ? '<button type="button" class="text-button" data-clear-filters>清除筛选</button>' : ''}</div>`;
  if (focused) Array.from(document.querySelectorAll<HTMLButtonElement>('[data-run-id]')).find(button => button.dataset.runId === focused)?.focus({ preventScroll: true });
  icons();
}
const visibleRuns = () => filterRuns(state.runs, state.query, state.filter);
function clearFilters() {
  state.query = ''; state.filter = 'all';
  field('run-search').value = ''; field('run-filter').value = 'all';
  renderRunList();
}
const currentRun = () => state.selectedRun?.id === state.selectedId ? state.selectedRun : state.runs.find(run => run.id === state.selectedId);
const downloadUrl = (id: string) => `/api/runs/${encodeURIComponent(id)}/download`;
function resultBanner(run: WebRun) {
  const value = status(run);
  const title = passed(run) ? '完整原题已通过独立验收'
    : activeRun(run) ? run.status === 'queued' ? '任务已排队' : '研究正在运行'
      : run.status === 'cancelled' ? '运行已取消'
        : run.status === 'error' ? '运行发生错误'
          : ['evaluated_failed', 'evaluated_rejected'].includes(run.result?.status ?? '') ? '完整原题验收未通过' : '运行已结束，完整原题尚未验收通过';
  return `<div class="result-banner ${value.tone}">${icon(value.symbol)}<div><h3>${title}</h3><p>${html(resultDescription(run))}</p></div></div>`;
}
function progressView(run: WebRun) {
  const progress = runProgress(run);
  const labels = { done: '已完成', active: '进行中', stopped: '已停止', error: '未通过', pending: '等待中', skipped: '未执行' };
  return `<section class="run-progress" aria-label="运行进度">
    <div class="progress-summary"><div><span class="progress-caption">运行进度</span><h3>${html(progress.phaseLabel)}</h3></div><div class="elapsed-summary"><span>总用时</span><strong class="mono" data-total-clock>${formatDuration(progress.elapsed)}</strong></div></div>
    ${activeRun(run) ? `<p class="progress-description">${html(resultDescription(run))}</p>` : ''}
    <ol class="progress-steps">${progress.steps.map((step, index) => `<li class="progress-step ${step.state}" ${step.state === 'active' ? 'aria-current="step"' : ''}>
      <span class="step-marker" aria-hidden="true">${step.state === 'done' ? icon('check') : step.state === 'active' ? '<span class="spinner"></span>' : step.state === 'error' ? icon('x') : String(index + 1).padStart(2, '0')}</span><span class="step-label">${step.label}</span><span class="step-state">${labels[step.state]}</span><span class="step-duration mono" data-stage-clock="${index}">${formatDuration(step.elapsed)}</span>
    </li>`).join('')}</ol>
    <div class="progress-budget">${icon('clock-3')}<span>解题预算 <strong class="mono">${formatDuration(run.maxRunSeconds * 1000)}</strong></span><span>研究用时 <strong class="mono" data-solving-clock>${progress.solvingElapsed === null ? '尚未开始' : formatDuration(progress.solvingElapsed)}</strong></span></div>
  </section>`;
}
function updateClocks() {
  const run = currentRun();
  if (!run || document.hidden) return;
  const progress = runProgress(run);
  const update = (selector: string, value: string) => {
    const target = document.querySelector(selector);
    if (target && target.textContent !== value) target.textContent = value;
  };
  update('[data-total-clock]', formatDuration(progress.elapsed));
  update('[data-solving-clock]', progress.solvingElapsed === null ? '尚未开始' : formatDuration(progress.solvingElapsed));
  progress.steps.forEach((step, index) => update(`[data-stage-clock="${index}"]`, formatDuration(step.elapsed)));
}
function resultDownloads(run: WebRun) {
  if (!run.result) return '';
  return `<div class="result-toolbar">${run.result.proof ? `<button type="button" class="button" data-action="download-proof">${icon('file-code-2')}下载 Lean</button>` : ''}<button type="button" class="button" data-action="download-report">${icon('file-json-2')}下载报告</button></div>`;
}
const fact = (label: string, value: unknown, mono = false) => `<div><dt>${label}</dt><dd${mono ? ' class="mono"' : ''}>${html(value)}</dd></div>`;
function overview(run: WebRun) {
  const provider = state.session?.providers.find(item => item.id === run.providerId);
  const environment = environmentInfo(run.environment);
  const latest = run.events.at(-1);
  return `${activeRun(run) ? '' : resultBanner(run)}${progressView(run)}${resultDownloads(run)}
    <div class="overview-section"><h3>研究任务</h3><p class="task-content">${html(run.task)}</p></div>
    <div class="overview-section"><h3>执行配置</h3><dl class="facts">${fact('证明环境', environmentName(run.environment))}${environment ? fact('Lean 版本', environment.toolchain, true) : ''}${environment?.mathlibRevision ? fact('Mathlib 版本', environment.mathlibRevision, true) : ''}${fact('服务商', provider?.name ?? run.providerId)}${fact('模型', run.model, true)}${fact('推理强度', run.effort)}${fact('协作模式', run.coordination === 'cooperative' ? '任务协作' : '独立并行')}${fact('Agent 数量', run.workers)}${fact('轮次上限', run.maxTurns)}${fact('解题预算', `${run.maxRunSeconds} 秒`)}${fact('创建时间', timestamp(run.createdAt))}${run.finishedAt ? fact('结束时间', timestamp(run.finishedAt)) : ''}</dl></div>
    <div class="overview-section"><h3>最近活动</h3>${latest ? `<div class="last-activity"><time datetime="${html(latest.at)}">${html(timestamp(latest.at, true))}</time><span>${html(latest.message)}</span></div>` : '<p class="task-content">暂无活动记录</p>'}</div>`;
}
const displayedSource = (run: WebRun) => state.sourceView !== 'input' && run.result?.proof ? run.result.proof : run.source;
function sourceView(run: WebRun) {
  const hasProof = Boolean(run.result?.proof);
  const showingProof = hasProof && state.sourceView !== 'input';
  const proofLabel = passed(run) ? '验收证明' : '候选源码';
  return `<div class="panel-topline source-topline">${hasProof ? `<div class="source-switch" role="group" aria-label="源码版本"><button type="button" data-source-view="proof" aria-pressed="${state.sourceView === 'proof'}">${proofLabel}</button><button type="button" data-source-view="input" aria-pressed="${state.sourceView === 'input'}">原始题目</button><button type="button" data-source-view="diff" aria-pressed="${state.sourceView === 'diff'}">差异对比</button></div>` : '<h3>原始题目</h3>'}<div class="source-actions"><button type="button" class="icon-button" data-action="copy-source" aria-label="复制${showingProof ? proofLabel : '原始题目'}" title="复制${showingProof ? proofLabel : '原始题目'}">${icon('copy')}</button>${showingProof ? `<button type="button" class="icon-button" data-action="download-proof" aria-label="下载 Lean" title="下载 Lean">${icon('download')}</button>` : ''}</div></div>${hasProof && state.sourceView === 'diff' ? sourceDiffView(run, proofLabel) : `<pre class="code-scroll" tabindex="0" aria-label="Lean 源码"><code>${html(displayedSource(run))}</code></pre>`}`;
}
function sourceDiffView(run: WebRun, proofLabel: string) {
  const before = run.source, after = run.result!.proof;
  const sourceChanged = sourceComparison?.runId !== run.id || sourceComparison.before !== before || sourceComparison.after !== after;
  if (sourceChanged || sourceComparison?.folded !== state.foldUnchanged) {
    sourceComparison = { runId: run.id, before, after, folded: state.foldUnchanged, result: compareSources(before, after, state.foldUnchanged) };
    if (sourceChanged) state.diffChange = 0;
  }
  const comparison = sourceComparison!.result;
  const heading = `<div class="diff-heading"><span>原始题目</span>${icon('arrow-right')}<span>${proofLabel}</span></div>`;
  if (comparison.status === 'identical') return `${heading}<div class="empty-state diff-identical" role="status">${icon('check-check')}<p>${comparison.lineEndingsChanged ? '仅换行格式不同' : '源码内容相同'}</p></div>`;
  if (comparison.status === 'unavailable') return `${heading}<div class="empty-state diff-unavailable" role="status">${icon('file-code-2')}<p>差异过多，无法生成对比</p></div>`;
  const seen = new Set<number>();
  const rows = comparison.rows.map(row => sourceDiffRow(row, seen)).join('');
  state.diffChange = Math.max(0, Math.min(state.diffChange, seen.size - 1));
  return `${heading}<div class="diff-toolbar"><div class="diff-counts"><span class="diff-count-added" aria-label="新增 ${comparison.added} 行">+${comparison.added}</span><span class="diff-count-removed" aria-label="删除 ${comparison.removed} 行">-${comparison.removed}</span></div><label class="diff-toggle"><input type="checkbox" id="diff-changes-only" ${state.foldUnchanged ? 'checked' : ''}><span>折叠未改动</span></label><div class="diff-navigation"><button type="button" class="icon-button" data-action="diff-prev" title="上一处更改" aria-label="上一处更改" ${state.diffChange === 0 || !seen.size ? 'disabled' : ''}>${icon('chevron-up')}</button><span id="diff-position" class="mono" aria-live="polite">${seen.size ? state.diffChange + 1 : 0}/${seen.size}</span><button type="button" class="icon-button" data-action="diff-next" title="下一处更改" aria-label="下一处更改" ${state.diffChange >= seen.size - 1 ? 'disabled' : ''}>${icon('chevron-down')}</button></div></div>
    <div class="diff-scroll" tabindex="0" aria-label="源码差异对比"><table class="diff-table"><caption class="sr-only">原始题目与${proofLabel}的逐行差异</caption><thead><tr><th scope="col">原始</th><th scope="col">${passed(run) ? '验收' : '候选'}</th><th scope="col">源码</th></tr></thead><tbody>${rows}</tbody></table></div>${comparison.omittedLines ? `<p class="diff-truncated" role="status">另有 ${comparison.omittedLines} 行未展示</p>` : ''}`;
}
function sourceDiffRow(row: SourceDiffRow, seen: Set<number>) {
  if (row.kind === 'gap') return `<tr class="diff-gap"><td colspan="3">${row.count} 行未改动</td></tr>`;
  const firstChange = row.changeId !== undefined && !seen.has(row.changeId);
  if (row.changeId !== undefined) seen.add(row.changeId);
  return `<tr class="diff-${row.kind}"${row.oldLine === undefined ? '' : ` data-old-line="${row.oldLine}"`}${row.newLine === undefined ? '' : ` data-new-line="${row.newLine}"`}${firstChange ? ` data-change-start="${row.changeId}"` : ''}>
    <td class="diff-line-no">${row.oldLine ?? ''}</td><td class="diff-line-no">${row.newLine ?? ''}</td><td class="diff-code"><span class="diff-marker" aria-hidden="true">${row.kind === 'added' ? '+' : row.kind === 'removed' ? '-' : ' '}</span><code data-diff-text>${html(row.text)}</code>${row.noNewline ? `<span class="diff-no-newline" data-eof-side="${row.kind === 'removed' ? 'old' : row.kind === 'added' ? 'new' : 'both'}">文件末尾无换行</span>` : ''}</td></tr>`;
}
function updateDiffNavigation(move = 0, align = false) {
  const scroll = document.querySelector<HTMLElement>('#detail-panel .diff-scroll');
  if (!scroll) return;
  const changes = Array.from(scroll.querySelectorAll<HTMLElement>('[data-change-start]'));
  state.diffChange = Math.max(0, Math.min(state.diffChange + move, changes.length - 1));
  element<HTMLButtonElement>('[data-action="diff-prev"]').disabled = !changes.length || state.diffChange === 0;
  element<HTMLButtonElement>('[data-action="diff-next"]').disabled = state.diffChange >= changes.length - 1;
  element('#diff-position').textContent = `${changes.length ? state.diffChange + 1 : 0}/${changes.length}`;
  changes.forEach((row, index) => row.classList.toggle('diff-change-current', index === state.diffChange));
  if ((move || align) && changes[state.diffChange]) {
    const headerHeight = scroll.querySelector('thead')?.getBoundingClientRect().height ?? 0;
    scroll.scrollTop += changes[state.diffChange].getBoundingClientRect().top - scroll.getBoundingClientRect().top - headerHeight;
  }
}
function reportView(run: WebRun) {
  if (!run.result) return run.error
    ? `${resultBanner(run)}<section class="report-section"><h3>运行诊断</h3><pre class="diagnostic-output" tabindex="0">${html(run.error)}</pre></section>`
    : `<div class="empty-state">${icon('file-json-2')}<p>${activeRun(run) ? '结果报告尚未生成' : '暂无结果报告'}</p></div>`;
  const toolbar = `<div class="panel-topline report-topline"><div class="source-switch" role="group" aria-label="报告视图"><button type="button" data-report-view="summary" aria-pressed="${state.reportMode === 'summary'}">验收摘要</button><button type="button" data-report-view="json" aria-pressed="${state.reportMode === 'json'}">JSON</button></div><div class="report-actions"><button type="button" class="icon-button" data-action="copy-report" aria-label="复制报告 JSON" title="复制报告 JSON">${icon('copy')}</button><button type="button" class="button" data-action="download-report">${icon('download')}下载报告</button></div></div>`;
  if (state.reportMode === 'json') return `${toolbar}<pre class="code-scroll report" tabindex="0" aria-label="结果报告 JSON"><code>${html(JSON.stringify(run.result.report, null, 2))}</code></pre>`;
  const report = summarizeReport(run);
  return `${toolbar}<div class="report-summary">${resultBanner(run)}
    ${report.reason ? `<section class="report-section report-reason"><h3>运行说明</h3><p>${html(report.reason)}</p></section>` : ''}
    ${report.metrics.length ? `<dl class="report-metrics">${report.metrics.map(item => fact(item.label, item.value, true)).join('')}</dl>` : ''}
    ${report.checks.length ? report.checks.map(reportCheck).join('') : '<div class="empty-state compact"><p>暂无结构化验收记录</p></div>'}
    ${report.identity.length ? `<section class="report-section"><h3>验收凭据</h3><dl class="facts report-identity">${report.identity.map(item => fact(item.label, item.value, true)).join('')}</dl></section>` : ''}</div>`;
}
function reportCheck(check: ReportCheck) {
  return `<section class="report-section" data-check-stage="${check.id}"><div class="report-check-heading"><h3>${html(check.label)}</h3><span class="badge ${check.tone}">${html(check.status)}</span></div>
    ${check.method ? `<p class="report-method">${html(check.method)}</p>` : ''}${check.reason ? `<p class="report-reason-text">${html(check.reason)}</p>` : ''}
    ${check.targets.length ? `<ul class="verification-targets">${check.targets.map(reportTarget).join('')}</ul>` : ''}
    ${check.omittedTargets ? `<p class="report-method">另有 ${check.omittedTargets} 个目标，详见原始报告</p>` : ''}</section>`;
}
function reportTarget(target: ReportTarget) {
  const counts = [target.sorryCount === undefined ? '' : `sorry ${target.sorryCount}`, target.admitCount === undefined ? '' : `admit ${target.admitCount}`].filter(Boolean).join(' · ');
  return `<li class="verification-target"><div class="target-heading"><code>${html(target.name)}</code><span class="badge ${target.tone}">${html(target.status)}</span></div>
    ${counts ? `<p class="target-counts mono">${html(counts)}</p>` : ''}
    ${target.diagnostics.length ? `<details class="target-diagnostics" ${target.tone === 'failed' ? 'open' : ''}><summary>诊断记录 <span class="field-count">${target.diagnostics.length}</span></summary>${target.diagnostics.map(diagnostic => `<div class="diagnostic-entry"><h4>${html(diagnostic.label)}</h4><pre class="diagnostic-output" tabindex="0">${html(diagnostic.text)}</pre></div>`).join('')}</details>` : ''}</li>`;
}
function eventsView(run: WebRun) {
  if (!run.events.length) return `<div class="empty-state">${icon('clock-3')}<p>暂无活动记录</p></div>`;
  return `<div class="panel-topline"><h3>活动记录</h3><span class="field-count">${run.events.length} 条</span></div><div class="activity-scroll" tabindex="0" aria-label="活动记录表"><table class="activity-table"><thead><tr><th scope="col">时间</th><th scope="col">事件</th><th scope="col">记录</th></tr></thead><tbody>${[...run.events].reverse().map(event => `<tr><td title="${html(event.at)}">${html(timestamp(event.at, true))}</td><td class="mono">${html(event.type)}</td><td>${html(event.message)}</td></tr>`).join('')}</tbody></table></div>`;
}
function renderPanel(force = false) {
  const run = currentRun();
  if (!run || !document.querySelector('#detail-panel')) return;
  const signature = JSON.stringify([run.id, state.tab, state.tab === 'source' ? [state.sourceView, state.foldUnchanged, run.status, run.source, run.result?.proof, run.result?.status]
    : state.tab === 'report' ? [state.reportMode, run.status, run.error, run.result] : state.tab === 'events' ? run.events : run]);
  if (!force && signature === state.panelSignature) return;
  state.panelSignature = signature;
  const panel = element('#detail-panel');
  const samePanel = panel.dataset.renderRunId === run.id && panel.dataset.tab === state.tab;
  const sameView = samePanel && (state.tab !== 'source' || panel.dataset.renderSourceView === state.sourceView);
  const previousScroll = panel.querySelector('.code-scroll,.activity-scroll,.diff-scroll');
  const scrollTop = sameView ? previousScroll?.scrollTop ?? 0 : 0;
  const scrollLeft = sameView ? previousScroll?.scrollLeft ?? 0 : 0;
  const focused = document.activeElement instanceof HTMLElement && panel.contains(document.activeElement)
    ? document.activeElement : undefined;
  const action = focused?.dataset.action;
  const sourceMode = focused?.dataset.sourceView;
  const reportMode = focused?.dataset.reportView;
  const focusId = focused?.id;
  panel.innerHTML = state.tab === 'source' ? sourceView(run) : state.tab === 'report' ? reportView(run) : state.tab === 'events' ? eventsView(run) : overview(run);
  panel.dataset.renderRunId = run.id; panel.dataset.tab = state.tab;
  panel.dataset.renderSourceView = state.sourceView;
  const scroll = panel.querySelector<HTMLElement>('.code-scroll,.activity-scroll,.diff-scroll');
  if (scroll) { scroll.scrollTop = scrollTop; scroll.scrollLeft = scrollLeft; }
  if (samePanel && action) panel.querySelector<HTMLElement>(`[data-action="${action}"]`)?.focus({ preventScroll: true });
  else if (samePanel && sourceMode) panel.querySelector<HTMLElement>(`[data-source-view="${sourceMode}"]`)?.focus({ preventScroll: true });
  else if (sameView && reportMode) panel.querySelector<HTMLElement>(`[data-report-view="${reportMode}"]`)?.focus({ preventScroll: true });
  else if (sameView && focused === previousScroll) scroll?.focus({ preventScroll: true });
  else if (samePanel && focusId) document.getElementById(focusId)?.focus({ preventScroll: true });
  icons();
  updateDiffNavigation(0, !sameView);
}
function renderDraftPreview() {
  if (currentRun() || !state.session) return;
  const detail = element('#run-detail');
  // Hidden panes cannot restore scroll offsets; refresh them when they become visible.
  if (!detail.getClientRects().length) return;
  const source = field('source').value, task = field('task').value;
  const template = state.session.templates.find(item => item.id === field('template').value && item.environment === field('environment').value);
  const environment = environmentInfo(field('environment').value);
  const numericLabel = (id: string, suffix: string) => {
    const value = Number(field(id).value);
    return field(id).value && Number.isSafeInteger(value) && value > 0 ? `${value} ${suffix}` : '未设置';
  };
  const facts = [
    ['environment', '证明环境', environment?.name ?? '未选择', false],
    ['model', '模型', field('model').value || '未设置', true],
    ['budget', '解题预算', numericLabel('max-seconds', '秒'), true],
    ['workers', 'Agent 数量', numericLabel('workers', '个'), true],
  ] as const;
  const title = template?.name ?? '自定义研究';
  const signature = JSON.stringify([title, source, task, facts]);
  if (signature === draftPreviewSignature && document.querySelector('#draft-preview')) return;
  draftPreviewSignature = signature;
  const lines = source.split('\n'), shown = lines.slice(0, 160);
  const previousScroll = detail.querySelector('.draft-source-scroll');
  const scrollTop = previousScroll?.scrollTop ?? 0, scrollLeft = previousScroll?.scrollLeft ?? 0;
  detail.innerHTML = `<div class="detail-empty draft-preview" id="draft-preview">
    <header class="preview-heading"><div><span class="preview-eyebrow">研究草稿</span><h2>${html(title)}</h2></div><span class="badge preview-status">${icon('file-code-2')}未提交</span></header>
    <dl class="preview-facts">${facts.map(([id, label, value, mono]) => `<div><dt>${label}</dt><dd data-preview-value="${id}"${mono ? ' class="mono"' : ''}>${html(value)}</dd></div>`).join('')}</dl>
    <section class="preview-source" aria-labelledby="preview-source-heading"><div class="preview-source-heading"><h3 id="preview-source-heading">${icon('file-code-2')}原始题目</h3><span>${lines.length > shown.length ? `前 ${shown.length} / ${lines.length}` : lines.length} 行 · ${byteLabel(byteSize(source))}</span></div>
      <div class="draft-source-scroll" tabindex="0" aria-label="原始题目草稿"><pre class="preview-line-numbers" aria-hidden="true">${shown.map((_, index) => index + 1).join('\n')}</pre><pre id="draft-preview-code"><code>${html(shown.join('\n'))}</code></pre></div>
    </section><section class="preview-task"><h3>研究任务</h3><p class="task-content" id="draft-preview-task">${html(task || '未填写')}</p></section></div>`;
  const scroll = detail.querySelector<HTMLElement>('.draft-source-scroll')!;
  scroll.scrollTop = scrollTop; scroll.scrollLeft = scrollLeft;
  icons();
}
function renderDetail(force = false) {
  const run = currentRun();
  if (sourceComparison && sourceComparison.runId !== run?.id) sourceComparison = undefined;
  if (!run) {
    state.detailSignature = ''; state.panelSignature = '';
    if (state.session) renderDraftPreview();
    else element('#run-detail').innerHTML = `<div class="empty-state detail-empty"><span class="spinner"></span><h2>正在连接工作台</h2></div>`;
    return;
  }
  const signature = JSON.stringify([run.id, run.title, run.status, run.phase, run.environment, run.updatedAt, run.result?.status, state.cancelling.has(run.id), state.deleting.has(run.id), state.detailError, state.connected]);
  const detail = element('#run-detail');
  const focused = document.activeElement instanceof HTMLElement && detail.contains(document.activeElement)
    ? document.activeElement : undefined;
  const focusId = focused?.id;
  const focusAction = focused?.dataset.action;
  if (force || signature !== state.detailSignature) {
    state.detailSignature = signature;
    const existingPanel = document.querySelector<HTMLElement>('#detail-panel');
    const existingScroll = existingPanel?.querySelector<HTMLElement>('.code-scroll,.activity-scroll,.diff-scroll');
    const scrollTop = existingScroll?.scrollTop ?? 0;
    const scrollLeft = existingScroll?.scrollLeft ?? 0;
    detail.innerHTML = `<header class="detail-heading"><div class="detail-heading-text"><h2>${html(run.title)}</h2><div class="detail-identifier"><code>${html(run.id)}</code><button type="button" class="icon-button" data-action="copy-id" aria-label="复制运行 ID" title="复制运行 ID">${icon('copy')}</button></div></div><div class="detail-actions"><button type="button" class="icon-button" data-action="reuse-run" aria-label="复用任务配置" title="复用任务配置">${icon('copy-plus')}</button>${activeRun(run) ? `<button type="button" class="button button-danger" data-action="cancel" ${state.cancelling.has(run.id) || !state.connected ? 'disabled' : ''}>${icon('square')}${state.cancelling.has(run.id) ? '正在取消' : '取消运行'}</button>` : `<button type="button" class="icon-button danger" data-action="delete-run" aria-label="删除运行记录" title="删除运行记录" ${!state.connected || state.deleting.has(run.id) ? 'disabled' : ''}>${icon('trash-2')}</button>`}${run.result || !activeRun(run) ? `<a class="icon-button" href="${downloadUrl(run.id)}" download title="下载运行档案 JSON" aria-label="下载运行档案 JSON">${icon('download')}</a>` : ''}</div></header>
      <div class="detail-statusline">${badge(run)}<span class="run-environment">${html(environmentName(run.environment))}</span><span class="updated-at">更新 ${html(timestamp(run.updatedAt))}</span></div>
      ${state.detailError ? `<div class="inline-error" role="alert">${html(state.detailError)}</div>` : ''}
      <div class="detail-tabs" role="tablist" aria-label="运行详情视图">${([['overview', '概览'], ['source', 'Lean 源码'], ['report', '报告'], ['events', '活动']] as const).map(([tab, label]) => `<button type="button" role="tab" id="detail-tab-${tab}" data-detail-tab="${tab}" aria-controls="detail-panel" aria-selected="${state.tab === tab}" tabindex="${state.tab === tab ? '0' : '-1'}">${label}</button>`).join('')}</div><div class="detail-panel" id="detail-panel" role="tabpanel" aria-labelledby="detail-tab-${state.tab}" tabindex="0"></div>`;
    if (existingPanel) {
      detail.querySelector('#detail-panel')?.replaceWith(existingPanel);
      existingPanel.setAttribute('aria-labelledby', `detail-tab-${state.tab}`);
      if (existingScroll) { existingScroll.scrollTop = scrollTop; existingScroll.scrollLeft = scrollLeft; }
    }
    icons();
  }
  if (focused?.isConnected) focused.focus({ preventScroll: true });
  renderPanel(force);
  if (focused?.isConnected) focused.focus({ preventScroll: true });
  else if (focusId) document.getElementById(focusId)?.focus({ preventScroll: true });
  else if (focusAction) detail.querySelector<HTMLElement>(`[data-action="${focusAction}"]`)?.focus({ preventScroll: true });
}
function selectRun(id: string) {
  if (!state.runs.some(run => run.id === id)) return;
  state.selectedId = id; state.selectedRun = state.runs.find(run => run.id === id);
  state.tab = 'overview'; state.sourceView = 'proof'; state.reportMode = 'summary'; state.detailError = ''; state.panelSignature = '';
  state.diffChange = 0;
  renderRunList(); renderDetail(true);
}
const currentConnection = (epoch: number) => pageActive && epoch === state.connectionEpoch;
const sessionFailure = (error: unknown) => error instanceof ApiError
  && (error.status === 401 || error.status === 403 && error.message.includes('会话校验'));
function invalidateReads() {
  state.connectionEpoch++;
  state.listGeneration++;
  readController.abort();
  readController = new AbortController();
  state.refreshing = false;
}
function disconnected(text: string) {
  state.connected = false;
  setGlobalNotice(text);
  element('#runs-error').textContent = '连接中断，记录可能不是最新状态';
  element('#runs-error').hidden = false;
  renderRuntime(); renderDetail();
}
async function refreshRuns(epoch: number) {
  const generation = ++state.listGeneration;
  const { runs } = await api<{ runs: WebRun[] }>('/api/runs');
  if (generation !== state.listGeneration || !currentConnection(epoch)) return;
  state.runs = runs.sort((a, b) => b.createdAt.localeCompare(a.createdAt));
  if (!state.selectedId || !state.runs.some(run => run.id === state.selectedId)) {
    state.selectedId = state.runs[0]?.id ?? '';
    state.tab = 'overview'; state.sourceView = 'proof'; state.reportMode = 'summary'; state.panelSignature = '';
  }
  state.selectedRun = state.runs.find(run => run.id === state.selectedId);
  state.detailError = '';
  element('#runs-error').hidden = true;
  renderRunList(); renderDetail(); renderDeleteState();
}
async function poll() {
  if (!pageActive) return;
  if (connectionRequest) return connectionRequest;
  if (!state.connected) return initialize();
  if (state.refreshing) return;
  const epoch = state.connectionEpoch;
  state.refreshing = true;
  element<HTMLButtonElement>('#refresh-runs').disabled = true;
  try { await refreshRuns(epoch); }
  catch (error) {
    if (!currentConnection(epoch)) return;
    disconnected(`${message(error)}。未提交内容已保留。`);
    if (sessionFailure(error)) await initialize();
  } finally {
    if (currentConnection(epoch)) state.refreshing = false;
    element<HTMLButtonElement>('#refresh-runs').disabled = !pageActive || Boolean(connectionRequest) || state.refreshing;
  }
}
function schedulePoll() {
  clearTimeout(pollTimer);
  if (!pageActive) return;
  pollTimer = setTimeout(async () => {
    if (!document.hidden) await poll();
    if (pageActive) schedulePoll();
  }, state.connected && state.runs.some(activeRun) ? 1800 : 5000);
}
function initialize(): Promise<void> {
  if (connectionRequest) return connectionRequest;
  if (!pageActive) return Promise.resolve();
  invalidateReads();
  const epoch = state.connectionEpoch;
  state.connected = false;
  element<HTMLButtonElement>('#retry-connection').disabled = true;
  element<HTMLButtonElement>('#refresh-runs').disabled = true;
  connectionRequest = (async () => {
    try {
      if (!navigator.onLine) throw new Error('网络已断开');
      const session = await api<WebSession>('/api/session');
      if (!currentConnection(epoch)) return;
      const firstLoad = !state.session;
      if (state.session && state.session.csrfToken !== session.csrfToken) {
        state.runs = []; state.selectedId = ''; state.selectedRun = undefined;
        state.detailError = ''; state.panelSignature = '';
        renderRunList(); renderDetail();
        toast('会话已更新，未提交内容已保留');
      }
      state.session = session;
      const previousProvider = field('provider').value;
      field('provider').innerHTML = session.providers.map(provider => `<option value="${html(provider.id)}">${html(provider.name)}</option>`).join('') || '<option value="">无可用服务商</option>';
      if (!firstLoad) field('provider').value = session.providers.some(provider => provider.id === previousProvider) ? previousProvider : '';
      const previousEnvironment = field('environment').value;
      field('environment').innerHTML = session.environments.map(environment => `<option value="${html(environment.id)}">${html(environment.name)}</option>`).join('');
      field('environment').value = session.environments.some(environment => environment.id === previousEnvironment) ? previousEnvironment : session.defaults.environment;
      renderTemplates(field('template').value);
      element<HTMLInputElement>('#max-turns').max = String(session.limits.maxTurns);
      element<HTMLInputElement>('#max-seconds').max = String(session.limits.maxRunSeconds);
      element<HTMLInputElement>('#workers').max = String(session.limits.maxWorkers);
      if (firstLoad) { resetForm(); restoreDraft(); draftReady = true; }
      providerAddress(); updateEnvironment(); updateCounts(); renderRuntime();
      await refreshRuns(epoch);
      if (!currentConnection(epoch)) return;
      state.connected = true;
      setGlobalNotice(session.runtime.ready && session.providers.length ? '' : session.runtime.message || '运行环境未就绪');
    } catch (error) {
      if (currentConnection(epoch)) {
        disconnected(`${message(error)}。未提交内容已保留。`);
        if (!state.session) renderRunList(true);
      }
    }
  })().finally(() => {
    connectionRequest = undefined;
    element<HTMLButtonElement>('#retry-connection').disabled = !pageActive;
    element<HTMLButtonElement>('#refresh-runs').disabled = !pageActive;
    renderRuntime(); renderDetail();
    if (pageActive && !clockTimer) clockTimer = setInterval(updateClocks, 1000);
    schedulePoll();
  });
  renderRuntime(); renderDetail();
  return connectionRequest;
}
function numberInput(id: string, max: number, min = 1) {
  const value = Number(field(id).value);
  if (!Number.isSafeInteger(value) || value < min || value > max) throw new Error(`执行配置超出允许范围：${min}–${max}`);
  return value;
}
element<HTMLFormElement>('#run-form').addEventListener('submit', async event => {
  event.preventDefault();
  const session = state.session;
  if (!session || !state.connected || state.submitting || !session.runtime.ready || !session.providers.length) return;
  const errorBox = element('#form-error'); errorBox.hidden = true;
  const epoch = state.connectionEpoch;
  let sent = false;
  if (!element<HTMLFormElement>('#run-form').reportValidity()) return;
  try {
    if (!session.providers.some(provider => provider.id === field('provider').value)) throw new Error('请选择可用的服务商');
    if (!session.environments.some(environment => environment.id === field('environment').value)) throw new Error('请选择可用的证明环境');
    if (!field('source').value.trim() || !field('task').value.trim() || !field('model').value.trim() || !field('api-key').value.trim()) throw new Error('请填写完整的模型连接与研究任务');
    if (byteSize(field('source').value) > session.limits.maxSourceBytes) throw new Error('Lean 源码超出允许大小');
    if (byteSize(field('task').value) > session.limits.maxTaskBytes) throw new Error('研究任务超出允许大小');
    const input: WebRunInput = {
      providerId: field('provider').value, apiKey: field('api-key').value.trim(), model: field('model').value.trim(),
      effort: field('effort').value as WebEffort, environment: field('environment').value as WebEnvironment,
      source: field('source').value, task: field('task').value,
      maxTurns: numberInput('max-turns', session.limits.maxTurns), maxRunSeconds: numberInput('max-seconds', session.limits.maxRunSeconds, 30),
      workers: numberInput('workers', session.limits.maxWorkers),
      coordination: element<HTMLInputElement>('input[name="coordination"]:checked').value as WebCoordination,
    };
    state.submitting = true; renderRuntime();
    sent = true;
    const { run } = await api<{ run: WebRun }>('/api/runs', { method: 'POST', body: JSON.stringify(input) });
    field('api-key').value = '';
    element<HTMLInputElement>('#api-key').type = 'password'; updateKeyToggle();
    if (!currentConnection(epoch)) {
      toast('研究已提交，连接已变化，请核对运行记录');
      void poll(); return;
    }
    state.listGeneration++;
    state.runs = [run, ...state.runs.filter(item => item.id !== run.id)];
    state.selectedId = run.id; state.selectedRun = run; state.tab = 'overview'; state.sourceView = 'proof'; state.reportMode = 'summary'; state.detailError = '';
    clearFilters();
    state.panelSignature = ''; renderRunList(); renderDetail(true); setMobileView('runs');
    schedulePoll();
    toast('研究已提交');
  } catch (error) {
    const key = field('api-key').value.trim();
    const uncertain = sent && (!(error instanceof ApiError) || error.status >= 500);
    const text = uncertain ? '提交结果尚未确认，请先核对运行记录后再决定是否重新提交。' : message(error);
    errorBox.textContent = key ? text.split(key).join('[已隐藏]') : text;
    errorBox.hidden = false;
    if (sent && currentConnection(epoch) && (uncertain || sessionFailure(error))) {
      disconnected('连接需要恢复，未提交内容已保留。');
      void initialize();
    }
  } finally { state.submitting = false; renderRuntime(); }
});
async function cancelRun() {
  const run = currentRun();
  if (!state.connected || !run || !activeRun(run) || state.cancelling.has(run.id)) return;
  const epoch = state.connectionEpoch;
  state.cancelling.add(run.id); renderDetail();
  try {
    const result = await api<{ run: WebRun }>(`/api/runs/${encodeURIComponent(run.id)}/cancel`, { method: 'POST' });
    if (!currentConnection(epoch)) { toast('取消请求已送达，请核对运行记录'); void poll(); return; }
    state.listGeneration++;
    const index = state.runs.findIndex(item => item.id === run.id);
    if (index >= 0) state.runs[index] = result.run;
    if (state.selectedId === run.id) state.selectedRun = result.run;
    toast('已请求取消运行');
  } catch (error) {
    const uncertain = !(error instanceof ApiError) || error.status >= 500;
    if (currentConnection(epoch)) {
      if (state.selectedId === run.id) state.detailError = uncertain ? '取消结果尚未确认，请核对最新运行状态。' : message(error);
      if (uncertain || sessionFailure(error)) {
        disconnected('连接需要恢复，请核对取消结果。'); void initialize();
      }
    }
    toast(uncertain ? '取消结果尚未确认' : `取消失败：${message(error)}`);
  } finally { state.cancelling.delete(run.id); renderRunList(); renderDetail(); }
}
function renderDeleteState() {
  if (!deletionTarget) return;
  const busy = state.deleting.has(deletionTarget.id);
  const run = state.runs.find(run => run.id === deletionTarget!.id);
  const sameSession = deletionTarget.csrfToken === state.session?.csrfToken;
  const notice = !sameSession ? '会话已变化，请关闭对话框。'
    : !state.connected ? '连接中断，恢复后可删除。'
      : !run ? '记录已不存在。' : activeRun(run) ? '任务尚未结束，不能删除。' : '';
  element('#delete-notice').textContent = notice;
  element('#delete-notice').hidden = !notice;
  element<HTMLButtonElement>('#confirm-delete').disabled = busy || Boolean(notice);
  element<HTMLButtonElement>('#cancel-delete').disabled = busy;
  element<HTMLButtonElement>('#close-delete').disabled = busy;
  element('#confirm-delete').innerHTML = `${busy ? '<span class="spinner"></span>' : icon('trash-2')}<span>${busy ? '正在删除' : '删除记录'}</span>`;
  icons();
}
function openDeletion(run: WebRun) {
  if (!state.connected || !state.session || activeRun(run) || state.deleting.has(run.id)) return;
  deletionTarget = { id: run.id, title: run.title, csrfToken: state.session.csrfToken };
  element('#delete-title').textContent = run.title;
  element('#delete-error').hidden = true;
  const archive = element<HTMLAnchorElement>('#delete-download');
  archive.hidden = false; archive.href = downloadUrl(run.id);
  renderDeleteState();
  element<HTMLDialogElement>('#delete-run-dialog').showModal();
  element('#cancel-delete').focus();
}
function removeLocalRun(id: string) {
  const index = visibleRuns().findIndex(run => run.id === id);
  state.listGeneration++;
  state.runs = state.runs.filter(run => run.id !== id);
  if (state.selectedId === id) {
    const visible = visibleRuns();
    state.selectedId = visible[Math.min(Math.max(index, 0), visible.length - 1)]?.id ?? state.runs[0]?.id ?? '';
    state.tab = 'overview'; state.sourceView = 'proof'; state.reportMode = 'summary'; state.detailError = ''; state.panelSignature = '';
  }
  state.selectedRun = state.runs.find(run => run.id === state.selectedId);
  renderRunList(); renderDetail();
  if (document.body.dataset.mobileView === 'runs') setMobileView('runs');
}
async function deleteRun() {
  const target = deletionTarget;
  if (!target || !state.connected || target.csrfToken !== state.session?.csrfToken || state.deleting.has(target.id)) return;
  const run = state.runs.find(run => run.id === target.id);
  if (!run || activeRun(run)) { renderDeleteState(); return; }
  const epoch = state.connectionEpoch;
  state.deleting.add(target.id);
  element('#delete-error').hidden = true;
  renderDeleteState(); renderDetail();
  try {
    await api<{ deletedId: string }>(`/api/runs/${encodeURIComponent(target.id)}`, { method: 'DELETE' });
    if (currentConnection(epoch)) removeLocalRun(target.id);
    else void poll();
    element<HTMLDialogElement>('#delete-run-dialog').close();
    toast('运行记录已删除');
  } catch (error) {
    if (error instanceof ApiError && error.status === 404 && currentConnection(epoch)) {
      removeLocalRun(target.id);
      element<HTMLDialogElement>('#delete-run-dialog').close();
      toast('记录已不存在');
    } else {
      const uncertain = !(error instanceof ApiError) || error.status >= 500;
      element('#delete-error').textContent = uncertain ? '删除结果尚未确认，请核对历史记录。' : message(error);
      element('#delete-error').hidden = false;
      if (currentConnection(epoch)) {
        if (uncertain || sessionFailure(error)) {
          disconnected('连接需要恢复，请核对删除结果。'); void initialize();
        } else void poll();
      }
    }
  } finally {
    state.deleting.delete(target.id); renderDeleteState(); renderRunList(); renderDetail();
  }
}
function download(name: string, content: string, type: string) {
  const url = URL.createObjectURL(new Blob([content], { type }));
  const link = document.createElement('a'); link.href = url; link.download = name;
  document.body.append(link); link.click(); link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
async function copyText(text: string, success: string) {
  try {
    if (!navigator.clipboard?.writeText) throw new Error('剪贴板不可用');
    await navigator.clipboard.writeText(text); toast(success);
  } catch { toast('无法访问剪贴板'); }
}
function reuseRun(run: WebRun) {
  const session = state.session;
  if (!session || state.submitting) return;
  field('provider').value = session.providers.some(provider => provider.id === run.providerId) ? run.providerId : '';
  field('environment').value = run.environment;
  renderTemplates();
  for (const [id, value] of Object.entries({ model: run.model, effort: run.effort, source: run.source, task: run.task,
    'max-turns': run.maxTurns, 'max-seconds': run.maxRunSeconds, workers: run.workers })) field(id).value = String(value);
  element<HTMLInputElement>(`input[name="coordination"][value="${run.coordination}"]`).checked = true;
  field('api-key').value = '';
  element<HTMLInputElement>('#api-key').type = 'password';
  updateKeyToggle(); providerAddress(); updateEnvironment(); sourceChanged();
  element('#form-error').hidden = true;
  setMobileView('compose');
  field('api-key').focus();
  toast('已载入原始题目与执行配置');
}
element('#run-detail').addEventListener('click', event => {
  const target = (event.target as Element).closest<HTMLElement>('[data-action],button[data-detail-tab],button[data-source-view],button[data-report-view]');
  if (!target) return;
  if (target.dataset.detailTab) {
    state.tab = target.dataset.detailTab as DetailTab;
    renderDetail(true); element(`#detail-tab-${state.tab}`).focus({ preventScroll: true }); return;
  }
  if (target.dataset.sourceView) {
    if (!['proof', 'input', 'diff'].includes(target.dataset.sourceView)) return;
    state.sourceView = target.dataset.sourceView as 'proof' | 'input' | 'diff';
    renderPanel(true); return;
  }
  if (target.dataset.reportView) {
    state.reportMode = target.dataset.reportView as 'summary' | 'json';
    renderPanel(true); return;
  }
  const run = currentRun();
  if (!run) return;
  if (target.dataset.action === 'cancel') void cancelRun();
  if (target.dataset.action === 'delete-run') openDeletion(run);
  if (target.dataset.action === 'copy-id') void copyText(run.id, '运行 ID 已复制');
  if (target.dataset.action === 'copy-source') void copyText(displayedSource(run), 'Lean 源码已复制');
  if (target.dataset.action === 'copy-report' && run.result) void copyText(JSON.stringify(run.result.report, null, 2), '报告 JSON 已复制');
  if (target.dataset.action === 'reuse-run') reuseRun(run);
  if (target.dataset.action === 'diff-prev') updateDiffNavigation(-1);
  if (target.dataset.action === 'diff-next') updateDiffNavigation(1);
  if (target.dataset.action === 'download-proof' && run.result?.proof) download(`${run.id}-Submission.lean`, run.result.proof, 'text/plain;charset=utf-8');
  if (target.dataset.action === 'download-report' && run.result) download(`${run.id}-report.json`, JSON.stringify(run.result.report, null, 2) + '\n', 'application/json');
});
element('#run-detail').addEventListener('change', event => {
  if ((event.target as HTMLElement).id !== 'diff-changes-only') return;
  state.foldUnchanged = (event.target as HTMLInputElement).checked;
  renderPanel(true); updateDiffNavigation(0, true);
});
element('#run-list').addEventListener('click', event => {
  if ((event.target as Element).closest('[data-clear-filters]')) { clearFilters(); field('run-search').focus(); return; }
  const button = (event.target as Element).closest<HTMLElement>('[data-run-id]');
  if (button?.dataset.runId) selectRun(button.dataset.runId);
});
document.querySelectorAll<HTMLButtonElement>('button[data-mobile-view]').forEach(button => button.addEventListener('click', () => setMobileView(button.dataset.mobileView as 'compose' | 'runs')));
document.addEventListener('keydown', event => {
  const target = event.target as HTMLElement;
  if (target.matches('[data-detail-tab]') && ['ArrowRight', 'ArrowLeft', 'Home', 'End'].includes(event.key)) {
    event.preventDefault();
    const tabs: DetailTab[] = ['overview', 'source', 'report', 'events'];
    const index = tabs.indexOf(state.tab);
    state.tab = event.key === 'Home' ? tabs[0] : event.key === 'End' ? tabs.at(-1)! : tabs[(index + (event.key === 'ArrowRight' ? 1 : tabs.length - 1)) % tabs.length];
    renderDetail(true); element(`#detail-tab-${state.tab}`).focus({ preventScroll: true });
  }
  if (target.matches('button[data-mobile-view]') && ['ArrowRight', 'ArrowLeft', 'Home', 'End'].includes(event.key)) {
    event.preventDefault(); setMobileView(event.key === 'Home' ? 'compose' : event.key === 'End' ? 'runs' : target.dataset.mobileView === 'compose' ? 'runs' : 'compose', true);
  }
  const runs = visibleRuns();
  if (target.matches('[data-run-id]') && ['ArrowDown', 'ArrowUp', 'Home', 'End'].includes(event.key) && runs.length) {
    event.preventDefault();
    const index = runs.findIndex(run => run.id === target.dataset.runId);
    const next = event.key === 'Home' ? 0 : event.key === 'End' ? runs.length - 1 : (index + (event.key === 'ArrowDown' ? 1 : runs.length - 1)) % runs.length;
    selectRun(runs[next].id);
    Array.from(document.querySelectorAll<HTMLButtonElement>('[data-run-id]')).find(button => button.dataset.runId === state.selectedId)?.focus();
  }
});
field('provider').addEventListener('change', providerAddress);
field('environment').addEventListener('change', () => {
  sourceRevision++;
  const usingTemplate = Boolean(field('template').value);
  renderTemplates('', usingTemplate);
  if (usingTemplate) applyTemplate(field('template').value);
  updateEnvironment();
});
field('template').addEventListener('change', () => applyTemplate(field('template').value));
for (const type of ['input', 'change']) element('#run-form').addEventListener(type, event => {
  const target = event.target as HTMLElement;
  if (target.id !== 'source') draftChanged(target.id !== 'api-key');
});
for (const id of ['source', 'task']) field(id).addEventListener('input', () => {
  field('template').value = '';
  if (id === 'source') sourceChanged(); else updateCounts();
});
element('#import-source').addEventListener('click', () => element<HTMLInputElement>('#source-file').click());
element<HTMLInputElement>('#source-file').addEventListener('change', async event => {
  const input = event.target as HTMLInputElement, file = input.files?.[0];
  input.value = '';
  if (!file || !state.session || state.submitting) return;
  const revision = ++sourceRevision;
  element('#source-error').hidden = true;
  try {
    const source = await readLeanFile(file, state.session.limits.maxSourceBytes);
    if (revision !== sourceRevision || state.submitting) { toast('草稿已变化，未导入文件'); return; }
    setCustomSource(source);
    toast('Lean 文件已载入');
  } catch (error) {
    if (revision !== sourceRevision) return;
    element('#source-error').textContent = message(error); element('#source-error').hidden = false;
  }
});
element('#expand-source').addEventListener('click', openEditor);
element('#import-task').addEventListener('click', () => element<HTMLInputElement>('#task-file').click());
element<HTMLInputElement>('#task-file').addEventListener('change', event => {
  const input = event.target as HTMLInputElement, file = input.files?.[0];
  input.value = '';
  if (file) void importTaskFile(file);
});
element('#export-draft').addEventListener('click', () => {
  if (!state.session || state.submitting) return;
  element('#draft-error').hidden = true;
  try { download('theoremos-draft.json', encodeTaskDraft(captureDraft()), 'application/json'); }
  catch (error) { element('#draft-error').textContent = message(error); element('#draft-error').hidden = false; }
});
for (const id of ['cancel-import', 'close-import']) element(`#${id}`).addEventListener('click', () => element<HTMLDialogElement>('#import-task-dialog').close());
element('#import-task-dialog').addEventListener('close', () => {
  pendingImport = undefined;
  element('#import-task').focus({ preventScroll: true });
});
element('#confirm-import').addEventListener('click', () => {
  const target = pendingImport;
  if (!target || !state.session || state.submitting || target.revision !== draftRevision) { renderImportState(); return; }
  applyTaskDraft(target.draft); saveDraft();
  element<HTMLDialogElement>('#import-task-dialog').close();
  setMobileView('compose'); field('api-key').focus();
  toast('研究任务已载入');
});
for (const id of ['close-editor', 'cancel-editor']) element(`#${id}`).addEventListener('click', () => element<HTMLDialogElement>('#source-editor').close());
element('#apply-editor').addEventListener('click', applyEditor);
element('#confirm-delete').addEventListener('click', () => void deleteRun());
for (const id of ['cancel-delete', 'close-delete']) element(`#${id}`).addEventListener('click', () => {
  if (!deletionTarget || !state.deleting.has(deletionTarget.id)) element<HTMLDialogElement>('#delete-run-dialog').close();
});
element('#delete-run-dialog').addEventListener('cancel', event => {
  if (deletionTarget && state.deleting.has(deletionTarget.id)) event.preventDefault();
});
element('#delete-run-dialog').addEventListener('close', () => {
  deletionTarget = undefined;
  const focus = document.querySelector<HTMLElement>('[data-action="delete-run"]')
    ?? document.querySelector<HTMLElement>('.run-row.selected') ?? element('#refresh-runs');
  focus.focus({ preventScroll: true });
});
field('expanded-source').addEventListener('input', () => { element('#editor-error').hidden = true; updateEditorCount(); });
field('run-search').addEventListener('input', () => { state.query = field('run-search').value; renderRunList(); });
field('run-filter').addEventListener('change', () => { state.filter = field('run-filter').value as RunFilter; renderRunList(); });
element('#clear-run-search').addEventListener('click', () => { state.query = ''; field('run-search').value = ''; renderRunList(); field('run-search').focus(); });
element('#toggle-key').addEventListener('click', () => {
  const key = element<HTMLInputElement>('#api-key'); key.type = key.type === 'password' ? 'text' : 'password'; updateKeyToggle();
});
element('#reset-form').addEventListener('click', resetForm);
element('#retry-connection').addEventListener('click', () => void initialize());
element('#refresh-runs').addEventListener('click', () => void poll());
window.matchMedia('(max-width:850px)').addEventListener('change', () => renderDraftPreview());
document.addEventListener('visibilitychange', () => { if (!document.hidden) void poll(); else saveDraft(); });
window.addEventListener('offline', () => {
  invalidateReads(); disconnected('网络已断开，未提交内容已保留。'); schedulePoll();
});
async function resumeConnection() {
  await connectionRequest;
  if (pageActive && !state.connected) await initialize();
}
window.addEventListener('online', () => void resumeConnection());
window.addEventListener('pagehide', () => {
  saveDraft();
  pageActive = false; invalidateReads(); state.connected = false;
  clearTimeout(pollTimer); clearInterval(clockTimer); clockTimer = undefined;
  field('api-key').value = ''; element<HTMLInputElement>('#api-key').type = 'password'; updateKeyToggle();
});
window.addEventListener('pageshow', event => {
  if (event.persisted) {
    pageActive = true; field('api-key').value = '';
    void resumeConnection();
  }
});
icons();
void initialize();
