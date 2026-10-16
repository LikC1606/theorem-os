import {
  createIcons, ArrowDownWideNarrow, ArrowUpRight, BadgeCheck, Blocks, BookOpen,
  CalendarDays, Check, ChevronRight, CircleCheck, Code, Copy, Download, FileCheck2, FileClock, FileCode2,
  Files, FlaskConical, GitBranch, GitCommitHorizontal, GitFork, Hash, Info, Link2,
  ListStart, Search, SearchX, ShieldCheck, Tag, Terminal,
} from 'lucide';
import catalog from 'virtual:archive';
import type { ArchiveRecord, ArchiveSource } from './types';

const iconSet = {
  ArrowDownWideNarrow, ArrowUpRight, BadgeCheck, Blocks, BookOpen, CalendarDays, Check,
  ChevronRight, CircleCheck, Code, Copy, Download, FileCheck2, FileClock, FileCode2, Files, FlaskConical,
  GitBranch, GitCommitHorizontal, GitFork, Hash, Info, Link2, ListStart, Search,
  SearchX, ShieldCheck, Tag, Terminal,
};
const icons = () => createIcons({ icons: iconSet, attrs: { 'aria-hidden': 'true' } });
const icon = (name: string) => `<i data-lucide="${name}"></i>`;
const html = (value: string | number) => String(value).replace(/[&<>"']/g, character => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
}[character]!));
const element = <T extends HTMLElement = HTMLElement>(selector: string) => {
  const result = document.querySelector<T>(selector);
  if (!result) throw new Error(`Missing page element: ${selector}`);
  return result;
};
const date = (value: string) => new Date(value).toISOString().slice(0, 10);
const timestamp = (value: string) => `${new Date(value).toISOString().slice(0, 16).replace('T', ' ')} UTC`;
const external = (url: string, label: string, className = 'inline-link') =>
  `<a class="${className}" href="${html(url)}" target="_blank" rel="noreferrer">${html(label)}${icon('arrow-up-right')}</a>`;
const accepted = (record: ArchiveRecord) => record.status === 'official_accepted';
const statusBadge = (record: ArchiveRecord) => `<span class="status-badge ${accepted(record) ? 'accepted' : 'progress'}">${icon(accepted(record) ? 'circle-check' : 'flask-conical')}${accepted(record) ? '官方已验收' : '研究快照'}</span>`;
const sourceBindingLabels = {
  matches: '与归档文件的源码哈希一致', differs: '检查投影与归档文件的哈希不同', unrecorded: '未记录源码哈希绑定',
};
const iconButton = (action: string, label: string, name: string, value?: string) =>
  `<button type="button" class="icon-button" data-action="${action}" ${value ? `data-value="${html(value)}"` : ''} aria-label="${label}" title="${label}">${icon(name)}</button>`;
const installCommand = [
  'git clone https://github.com/LikC1606/theorem-os.git',
  'cd theorem-os',
  'bun install --frozen-lockfile',
].join('\n');
const replayCommand = [
  'elan toolchain install leanprover/lean4:v4.33.0',
  'bun run math doctor --lean-only',
  '',
  'export THEOREMOS_CASE="$PWD/../theorem-os-runs/first-replay"',
  'bun run math example replay --dir "$THEOREMOS_CASE"',
  'bun run math inspect --run "$THEOREMOS_CASE/result.json"',
].join('\n');

type Filter = 'all' | 'accepted' | 'progress';
type Sort = 'verified' | 'recent' | 'title';
type Tab = 'overview' | 'source' | 'evidence';
const state = {
  view: 'archive', filter: 'all' as Filter, query: '', sort: 'verified' as Sort,
  selected: catalog.records.find(accepted)?.id ?? catalog.records[0]?.id ?? '',
  tab: 'overview' as Tab, sourceName: '',
};
const selectedRecord = () => catalog.records.find(record => record.id === state.selected);

function readLocation() {
  const params = new URLSearchParams(location.hash.slice(1));
  state.view = params.get('view') === 'quickstart' ? 'quickstart' : 'archive';
  state.filter = ['accepted', 'progress'].includes(params.get('status') ?? '') ? params.get('status') as Filter : 'all';
  state.query = params.get('q') ?? '';
  state.sort = ['title', 'recent'].includes(params.get('sort') ?? '') ? params.get('sort') as Sort : 'verified';
  state.tab = ['source', 'evidence'].includes(params.get('tab') ?? '') ? params.get('tab') as Tab : 'overview';
  const id = params.get('proof');
  state.selected = catalog.records.find(record => record.id === id)?.id ?? catalog.records.find(accepted)?.id ?? '';
  state.sourceName = '';
}

function writeLocation(push = false) {
  const params = new URLSearchParams();
  if (state.view === 'quickstart') params.set('view', 'quickstart');
  else {
    if (state.selected) params.set('proof', state.selected);
    if (state.tab !== 'overview') params.set('tab', state.tab);
    if (state.filter !== 'all') params.set('status', state.filter);
    if (state.query) params.set('q', state.query);
    if (state.sort !== 'verified') params.set('sort', state.sort);
  }
  const url = `#${params.toString() || 'view=archive'}`;
  if (push) history.pushState(null, '', url);
  else history.replaceState(null, '', url);
}

function filteredRecords() {
  const query = state.query.trim().toLocaleLowerCase().replaceAll('_', ' ');
  return catalog.records.filter(record => {
    const matchesStatus = state.filter === 'all' || (state.filter === 'accepted' ? accepted(record) : !accepted(record));
    const text = `${record.title} ${record.subtitle} ${record.area} ${record.id} ${record.model}`.toLocaleLowerCase().replaceAll('_', ' ');
    return matchesStatus && (!query || text.includes(query));
  }).sort((a, b) => {
    if (state.sort === 'title') return a.title.localeCompare(b.title, 'en');
    if (state.sort === 'verified' && accepted(a) !== accepted(b)) return accepted(a) ? -1 : 1;
    return new Date(b.updatedAt).getTime() - new Date(a.updatedAt).getTime();
  });
}

function renderList(records: ArchiveRecord[]) {
  element('#proof-list').innerHTML = records.map(record => `
    <li><button type="button" class="proof-row ${state.selected === record.id ? 'is-selected' : ''}"
      data-proof-id="${record.id}" aria-pressed="${state.selected === record.id}"
      aria-label="${html(record.title)}，${accepted(record) ? '官方已验收' : '尚未官方验收'}">
      <span class="row-symbol ${accepted(record) ? '' : 'progress'}">${icon(accepted(record) ? 'file-check-2' : 'file-clock')}</span>
      <span><span class="row-title">${html(record.title)}</span><span class="row-subtitle">${html(record.subtitle)}<span class="area-label">${html(record.area)}</span></span></span>
      <span class="row-end">${statusBadge(record)}<span class="row-date">${date(record.updatedAt)}</span></span>
    </button></li>`).join('');
  element('#empty-state').hidden = records.length > 0;
  element('#result-count').textContent = `${records.length} 条记录${state.query ? ` · “${state.query}”` : ''}`;
}

function declaration(record: ArchiveRecord) {
  const source = record.sources.find(file => file.name === (accepted(record) ? 'Submission.lean' : 'Challenge.lean')) ?? record.sources[0];
  const lines = source.code.split('\n');
  const start = Math.max(0, lines.findIndex(line => record.declaration && line.startsWith(record.declaration)));
  return lines.slice(start, start + 7).join('\n');
}

const taskColors: Record<string, { label: string; color: string }> = {
  completed: { label: '完成', color: '#72a38d' }, integrated: { label: '集成', color: '#438564' },
  pending: { label: '待处理', color: '#d6dfda' }, blocked: { label: '受阻', color: '#c6a36a' },
  running: { label: '进行中', color: '#8898bd' },
};
function taskChart(record: ArchiveRecord) {
  if (!record.snapshot) return '';
  const tasks = Object.entries(record.snapshot.taskStatuses).filter(([, count]) => count > 0);
  return `<div class="detail-section"><div class="section-title"><h3>任务状态（快照）</h3><span>非整题验收进度</span></div>
    <div class="task-chart" role="img" aria-label="${html(tasks.map(([key, count]) => `${taskColors[key]?.label ?? key} ${count}`).join('，'))}">
      ${tasks.map(([key, count]) => `<span style="flex:${count};background:${taskColors[key]?.color ?? '#d6dfda'}"></span>`).join('')}
    </div><div class="task-legend">${tasks.map(([key, count]) => `<span><i style="background:${taskColors[key]?.color ?? '#d6dfda'}"></i>${html(taskColors[key]?.label ?? key)} ${count}</span>`).join('')}</div></div>`;
}

function overview(record: ArchiveRecord) {
  const local = record.local;
  return `<p class="detail-summary">${html(record.summary)}</p>
    ${!accepted(record) ? `<div class="draft-note">${icon('info')}<span>尚未官方验收。快照可能包含 sorry、失败方案或未检查的修改。</span></div>` : ''}
    <dl class="record-facts">
      <div><dt>原始归属</dt><dd>${html(record.model)}</dd></div>
      <div><dt>${accepted(record) ? '官方验收' : '快照记录'}</dt><dd class="mono">${timestamp(record.updatedAt)}</dd></div>
      ${record.official ? `<div><dt>题目版本</dt><dd>Statement revision ${record.official.statementRevision}</dd></div>
        <div><dt>原始提交</dt><dd>${external(record.official.sourceUrl, record.official.sourceCommit.slice(0, 12), 'inline-link mono')}</dd></div>` : ''}
      ${record.snapshot ? `<div><dt>快照阶段</dt><dd class="mono">${html(record.snapshot.phase)}</dd></div>
        <div><dt>研究记录</dt><dd>${record.snapshot.turns} 轮 · ${record.snapshot.workers} 个 worker</dd></div>` : ''}
      <div><dt>Lean 源码</dt><dd>${record.sources.length} 个文件 · ${record.sources.reduce((sum, source) => sum + source.lines, 0).toLocaleString('en')} 行</dd></div>
      ${local ? `<div><dt>本地记录</dt><dd>${html(local.status)}<span class="subfact">${sourceBindingLabels[local.sourceBinding]}</span></dd></div>` : ''}
    </dl>
    ${taskChart(record)}
    <div class="detail-section"><div class="section-title"><h3>${accepted(record) ? '目标声明 / 证明节选' : '原题声明节选'}</h3><span>Lean</span></div><pre class="declaration-preview">${html(declaration(record))}</pre></div>
    <div class="detail-links">${record.official ? external(record.official.resultUrl, '官方验收', 'button') : ''}${external(record.archiveUrl, '原始档案', 'button')}</div>`;
}

function currentSource(record: ArchiveRecord): ArchiveSource {
  return record.sources.find(source => source.name === state.sourceName) ??
    record.sources.find(source => source.name === (accepted(record) ? 'Submission.lean' : 'Challenge.lean')) ?? record.sources[0];
}

function sourceView(record: ArchiveRecord) {
  const source = currentSource(record);
  state.sourceName = source.name;
  const lines = source.code.split('\n');
  if (lines.at(-1) === '') lines.pop();
  return `<div class="source-toolbar"><label class="sr-only" for="source-file">Lean 文件</label>
      <select id="source-file">${record.sources.map(file => `<option value="${html(file.name)}" ${file.name === source.name ? 'selected' : ''}>${html(file.name)}</option>`).join('')}</select>
      ${iconButton('jump-declaration', '定位目标声明', 'list-start')}${iconButton('copy-source', '复制 Lean 源码', 'copy')}${iconButton('download-source', '下载 Lean 文件', 'download')}
    </div>
    <pre class="source-code" tabindex="0" aria-label="${html(source.name)} 源码"><code>${lines.map((line, index) => `<span class="code-line ${record.declaration && line.startsWith(record.declaration) ? 'is-declaration' : ''}"><span class="line-number" aria-hidden="true">${index + 1}</span><span>${html(line) || ' '}</span></span>`).join('')}</code></pre>
    <p class="source-facts"><strong>${source.lines.toLocaleString('en')} lines · SHA-256</strong><br>${source.sha256}</p>
    <div class="detail-links">${external(source.url, 'GitHub 原文件', 'button')}${iconButton('copy-hash', '复制文件 SHA-256', 'hash', source.sha256)}</div>`;
}

function evidence(record: ArchiveRecord) {
  if (!record.official) {
    return `<div class="evidence-entry"><h3>研究快照</h3><p>${timestamp(record.updatedAt)}</p><p>尚无官方验收通过记录。局部任务或引理检查不代表完整题目已解出。</p>${external(record.archiveUrl, '查看快照与 manifest')}</div>
      <dl class="record-facts"><div><dt>Run ID</dt><dd class="mono">${html(record.snapshot?.runId ?? '')}</dd></div></dl>${taskChart(record)}`;
  }
  const official = record.official;
  const local = record.local;
  return `<div class="evidence-entry"><h3>Lean-Eval 官方验收</h3><p>${timestamp(record.updatedAt)}</p>${external(official.resultUrl, '查看官方结果', 'inline-link official-result-link')}
    <pre class="evidence-body">${html(official.resultBody)}</pre></div>
    ${local ? `<div class="evidence-entry"><h3>归档本地验证记录</h3><p class="mono">${html(local.status)}<br>kernel_verified: ${local.kernelVerified}<br>comparator: ${html(local.comparator ?? '未记录')}</p>
      ${local.receipt ? `<p class="mono">receipt: ${html(local.receipt)}</p>` : ''}<p>Axioms: ${html(local.axioms.join(', ') || '未记录')}</p>
      ${local.sourceProofCommit ? `<p class="mono">proof commit: ${html(local.sourceProofCommit)}</p>` : ''}
      ${local.sourceBinding === 'differs' ? '<p class="binding-note">此记录的源码哈希与当前归档不同。官方验收以官方结果链接为准。</p>' : `<p>${sourceBindingLabels[local.sourceBinding]}</p>`}
      ${external(local.url, 'verification.json')}</div>` : ''}
    <div class="evidence-entry"><h3>原始提交来源</h3><p class="mono">${html(official.sourceCommit)}</p>${external(official.sourceUrl, '原始提交')}${external(official.submissionUrl, '提交讨论')}</div>
    ${local?.production ? `<details class="production-note"><summary>来源与人工参与</summary><p><span class="note-label">Production</span>${html(local.production.mode)}</p>
      ${local.production.freshFromZero === false ? '<p>此结果包含已保存候选的恢复或续跑。</p>' : ''}
      ${local.production.humanDirection ? `<p><span class="note-label">Human direction</span>${html(local.production.humanDirection)}</p>` : ''}</details>` : ''}
    <div class="detail-section"><div class="section-title"><h3>归档文件校验</h3><span>SHA-256</span></div><dl class="checksum-list">${Object.entries(official.checksums).map(([file, digest]) => `<dt>${html(file)}${iconButton('copy-hash', `复制 ${file} 校验值`, 'copy', digest)}</dt><dd>${digest}</dd>`).join('')}</dl></div>`;
}

function renderInspector(record?: ArchiveRecord) {
  if (!record) {
    element('#inspector').innerHTML = `<div class="inspector-empty">${icon('files')}<span>没有可显示的记录</span></div>`;
    return;
  }
  element('#inspector').innerHTML = `<div class="detail-topline"><span class="detail-topline-label">${icon('files')}档案详情</span><div class="detail-actions">${iconButton('copy-link', '复制题目链接', 'link-2')}${iconButton('download-record', '下载此题档案 JSON', 'download')}</div></div>
    <h2 class="detail-title">${html(record.title)}</h2><p class="detail-subtitle">${html(record.subtitle)}</p><p class="detail-id">${record.id}</p>
    <div class="detail-statusline">${statusBadge(record)}<span>Lean-Eval · ${html(record.area)}</span></div>
    <div class="detail-tabs" role="tablist" aria-label="档案详情视图">${([
      ['overview', '概览'], ['source', 'Lean 源码'], ['evidence', '验证证据'],
    ] as const).map(([tab, label]) => `<button type="button" role="tab" id="tab-${tab}" aria-controls="detail-panel" aria-selected="${state.tab === tab}" tabindex="${state.tab === tab ? 0 : -1}" data-tab="${tab}">${label}</button>`).join('')}</div>
    <div class="detail-panel" id="detail-panel" role="tabpanel" tabindex="0" aria-labelledby="tab-${state.tab}">${state.tab === 'overview' ? overview(record) : state.tab === 'source' ? sourceView(record) : evidence(record)}</div>`;
  if (state.tab === 'source') requestAnimationFrame(() => jumpToDeclaration(record));
}

function jumpToDeclaration(record: ArchiveRecord) {
  const source = currentSource(record);
  const start = source.code.split('\n').findIndex(line => record.declaration && line.startsWith(record.declaration));
  const panel = document.querySelector<HTMLElement>('.source-code');
  if (panel) panel.scrollTop = Math.max(0, start - 3) * 20;
}

function render() {
  const records = filteredRecords();
  if (!records.some(record => record.id === state.selected)) {
    state.selected = records[0]?.id ?? '';
    state.sourceName = '';
  }
  element('#archive-view').hidden = state.view !== 'archive';
  element('#quickstart-view').hidden = state.view !== 'quickstart';
  document.querySelectorAll<HTMLAnchorElement>('[data-view-link]').forEach(link => {
    const active = link.dataset.viewLink === state.view;
    link.classList.toggle('is-active', active);
    if (active) link.setAttribute('aria-current', 'page'); else link.removeAttribute('aria-current');
  });
  element<HTMLInputElement>('#search').value = state.query;
  element<HTMLSelectElement>('#sort').value = state.sort;
  document.querySelectorAll<HTMLInputElement>('input[name="status"]').forEach(input => input.checked = input.value === state.filter);
  renderList(records);
  renderInspector(selectedRecord());
  icons();
  writeLocation();
}

let toastTimeout: ReturnType<typeof setTimeout>;
function toast(message: string) {
  const notification = element('#toast');
  notification.textContent = message;
  notification.hidden = false;
  clearTimeout(toastTimeout);
  toastTimeout = setTimeout(() => notification.hidden = true, 2400);
}

async function copy(value: string) {
  try {
    if (navigator.clipboard?.writeText) await navigator.clipboard.writeText(value);
    else {
      const field = document.createElement('textarea');
      field.value = value;
      field.style.position = 'fixed';
      field.style.opacity = '0';
      document.body.append(field);
      field.select();
      const copied = document.execCommand('copy');
      field.remove();
      if (!copied) throw new Error('Clipboard unavailable');
    }
    toast('已复制');
  } catch {
    toast('复制失败，请检查浏览器剪贴板权限');
  }
}

function download(name: string, content: string, type: string) {
  const url = URL.createObjectURL(new Blob([content], { type }));
  const link = document.createElement('a');
  link.href = url;
  link.download = name;
  document.body.append(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

document.addEventListener('click', event => {
  const target = (event.target as Element).closest<HTMLElement>('[data-proof-id], [data-tab], [data-action], [data-view-link]');
  if (!target) return;
  if (target.dataset.viewLink) {
    event.preventDefault();
    state.view = target.dataset.viewLink;
    writeLocation(true);
    render();
    return;
  }
  if (target.dataset.proofId) {
    state.selected = target.dataset.proofId;
    state.sourceName = '';
    render();
    element(`[data-proof-id="${state.selected}"]`).focus({ preventScroll: true });
    if (matchMedia('(max-width: 700px)').matches) element('#inspector').scrollIntoView({ block: 'start' });
    return;
  }
  if (target.dataset.tab) {
    state.tab = target.dataset.tab as Tab;
    renderInspector(selectedRecord());
    icons();
    writeLocation();
    element(`#tab-${state.tab}`).focus({ preventScroll: true });
    return;
  }
  const record = selectedRecord();
  switch (target.dataset.action) {
    case 'quickstart': state.view = 'quickstart'; writeLocation(true); render(); break;
    case 'reset': state.query = ''; state.filter = 'all'; render(); element('#search').focus(); break;
    case 'copy-link': void copy(location.href); break;
    case 'copy-install': void copy(installCommand); break;
    case 'copy-replay': void copy(replayCommand); break;
    case 'copy-hash': void copy(target.dataset.value ?? ''); break;
    case 'jump-declaration': if (record) jumpToDeclaration(record); break;
    case 'copy-source': if (record) void copy(currentSource(record).code); break;
    case 'download-source': if (record) download(`${record.id}-${currentSource(record).name.replaceAll('/', '-')}`, currentSource(record).code, 'text/plain;charset=utf-8'); break;
    case 'download-record': if (record) download(`${record.id}.json`, JSON.stringify(record, null, 2), 'application/json'); break;
  }
});

element<HTMLInputElement>('#search').addEventListener('input', event => {
  state.query = (event.target as HTMLInputElement).value;
  render();
});
element<HTMLSelectElement>('#sort').addEventListener('change', event => {
  state.sort = (event.target as HTMLSelectElement).value as Sort;
  render();
});
document.querySelectorAll<HTMLInputElement>('input[name="status"]').forEach(input => input.addEventListener('change', () => {
  state.filter = input.value as Filter;
  render();
}));
element('#inspector').addEventListener('change', event => {
  if ((event.target as HTMLElement).id !== 'source-file') return;
  state.sourceName = (event.target as HTMLSelectElement).value;
  renderInspector(selectedRecord());
  icons();
  element('#source-file').focus({ preventScroll: true });
});
document.addEventListener('keydown', event => {
  const target = event.target as HTMLElement;
  if (target.matches('[data-tab]') && ['ArrowRight', 'ArrowLeft', 'Home', 'End'].includes(event.key)) {
    event.preventDefault();
    const tabs: Tab[] = ['overview', 'source', 'evidence'];
    const index = tabs.indexOf(state.tab);
    state.tab = event.key === 'Home' ? 'overview' : event.key === 'End' ? 'evidence' : tabs[(index + (event.key === 'ArrowRight' ? 1 : 2)) % 3];
    renderInspector(selectedRecord());
    icons();
    writeLocation();
    element(`#tab-${state.tab}`).focus({ preventScroll: true });
  }
  if (target.matches('[data-proof-id]') && ['ArrowDown', 'ArrowUp', 'Home', 'End'].includes(event.key)) {
    event.preventDefault();
    const records = filteredRecords();
    const current = records.findIndex(record => record.id === state.selected);
    const index = event.key === 'Home' ? 0 : event.key === 'End' ? records.length - 1 :
      (current + (event.key === 'ArrowDown' ? 1 : records.length - 1)) % records.length;
    state.selected = records[index].id;
    state.sourceName = '';
    render();
    element(`[data-proof-id="${state.selected}"]`).focus();
  }
});
window.addEventListener('hashchange', () => {
  if (!location.hash.includes('=')) return;
  readLocation();
  render();
});
window.addEventListener('popstate', () => { readLocation(); render(); });

const acceptedCount = catalog.records.filter(accepted).length;
const counts: Record<string, string> = {
  '#nav-count': String(catalog.records.length), '#all-filter-count': String(catalog.records.length),
  '#accepted-count': String(acceptedCount), '#accepted-filter-count': String(acceptedCount),
  '#progress-count': String(catalog.records.length - acceptedCount), '#progress-filter-count': String(catalog.records.length - acceptedCount),
  '#line-count': catalog.records.reduce((sum, record) => sum + record.sources.reduce((count, source) => count + source.lines, 0), 0).toLocaleString('en'),
  '#snapshot-date': date(catalog.snapshotAt),
};
for (const [selector, value] of Object.entries(counts)) element(selector).textContent = value;
element('#archive-revision').textContent = catalog.archiveRevision.slice(0, 7);
element<HTMLAnchorElement>('#archive-revision').href = `${catalog.repository}/commit/${catalog.archiveRevision}`;
element('#install-command').textContent = installCommand;
element('#replay-command').textContent = replayCommand;
readLocation();
render();
