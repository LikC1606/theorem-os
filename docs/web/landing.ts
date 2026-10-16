import {
  createIcons, ArrowDown, ArrowDownRight, ArrowRight, ArrowUpRight, Blocks, Check, Code2,
  Copy, FileCode2, Fingerprint, GitBranch, GitFork, History, Info,
  Menu, Pause, Play, Plus, ScanLine, ShieldCheck, Terminal, X,
} from 'lucide';

const iconSet = { ArrowDown, ArrowDownRight, ArrowRight, ArrowUpRight, Blocks, Check, Code2, Copy,
  FileCode2, Fingerprint, GitBranch, GitFork, History, Info, Menu, Pause, Play, Plus,
  ScanLine, ShieldCheck, Terminal, X };
const icons = () => createIcons({ icons: iconSet, attrs: { 'aria-hidden': 'true' } });
const element = <T extends HTMLElement = HTMLElement>(selector: string): T => {
  const result = document.querySelector<T>(selector);
  if (!result) throw new Error(`Missing landing page element: ${selector}`);
  return result;
};
icons();
document.documentElement.classList.add('js');

const components = {
  m1: { kicker: 'M1 / PROOF CONSTRUCTION', title: '把想法，写成候选证明。',
    description: '调用模型会话，在隔离工作区中构造和修复 Lean 候选。研究你的生成方式、提示和修复策略。',
    input: '题目 · 上下文 · 操作 · 模型会话', output: '候选记录 · 工作区中的证明', path: 'M104 70 290 118' },
  m2: { kicker: 'M2 / CHECKS & FEEDBACK', title: '让诊断，成为研究线索。',
    description: '检查候选与辅助证明，把 Lean 诊断交还研究过程。局部检查之后，集成结果仍需接受完整原题的独立验收。',
    input: '固定题目 · 候选源码 · 检查环境', output: '绑定源码摘要的检查与诊断', path: 'M476 70 290 118' },
  m3: { kicker: 'M3 / SEARCH POLICY', title: '让下一步，有章可循。',
    description: '选择就绪任务，决定继续、重试或停止。把任务排序与路线、预算约束放在一起研究。',
    input: '研究状态 · 候选操作 · 共享预算', output: '下一步操作 · 有序就绪任务', path: 'M290 34V118' },
  m4: { kicker: 'M4 / CONTEXT SELECTION', title: '把相关证据，带入思考。',
    description: '从题目、已有成果与失败记录中整理上下文。比较信息选择、上下文压缩和检索策略。',
    input: '题目 · 当前任务 · 可见证据', output: '带来源身份的上下文包', path: 'M128 194 290 118' },
  m5: { kicker: 'M5 / COOPERATION & REUSE', title: '让分工与交接，可以研究。',
    description: '组织隔离工作区、任务分配与独立审阅。比较单 Agent、独立并行与任务协作的研究方法。',
    input: '就绪任务 · Worker · 路线约束', output: '工作区配置 · 任务与审阅分配', path: 'M452 194 290 118' },
};
type Component = keyof typeof components;
const componentTabs = Array.from(document.querySelectorAll<HTMLButtonElement>('[data-component]'));
function selectComponent(id: Component, focus = false) {
  const content = components[id];
  if (!content) return;
  for (const tab of componentTabs) {
    const selected = tab.dataset.component === id;
    tab.setAttribute('aria-selected', String(selected));
    tab.tabIndex = selected ? 0 : -1;
    if (selected && focus) tab.focus();
  }
  element('#component-panel').setAttribute('aria-labelledby', `tab-${id}`);
  for (const [key, value] of Object.entries({ kicker: content.kicker, title: content.title,
    description: content.description, input: content.input, output: content.output })) {
    element(`#module-${key}`).textContent = value;
  }
  document.querySelectorAll<HTMLElement>('[data-diagram]').forEach(node => node.classList.toggle('is-active', node.dataset.diagram === id));
  document.querySelector('.module-active-path')!.setAttribute('d', content.path);
}
componentTabs.forEach(tab => tab.addEventListener('click', () => selectComponent(tab.dataset.component as Component)));

function handleTabKeys(event: KeyboardEvent, tabs: HTMLButtonElement[], select: (tab: HTMLButtonElement) => void) {
  const index = tabs.indexOf(event.target as HTMLButtonElement);
  if (index < 0) return;
  let next: number;
  if (['ArrowRight', 'ArrowDown'].includes(event.key)) next = (index + 1) % tabs.length;
  else if (['ArrowLeft', 'ArrowUp'].includes(event.key)) next = (index - 1 + tabs.length) % tabs.length;
  else if (event.key === 'Home') next = 0;
  else if (event.key === 'End') next = tabs.length - 1;
  else return;
  event.preventDefault();
  select(tabs[next]);
}

const replayTabs = Array.from(document.querySelectorAll<HTMLButtonElement>('[data-replay-stage]'));
function selectReplayStage(tab: HTMLButtonElement, focus = false) {
  for (const stage of replayTabs) {
    const selected = stage === tab;
    stage.setAttribute('aria-selected', String(selected));
    stage.tabIndex = selected ? 0 : -1;
    element(`#stage-${stage.dataset.replayStage}`).hidden = !selected;
  }
  if (focus) tab.focus();
}
replayTabs.forEach(tab => tab.addEventListener('click', () => selectReplayStage(tab)));
element('.replay-tabs').addEventListener('keydown', event => handleTabKeys(event, replayTabs, tab => selectReplayStage(tab, true)));

element('.component-tabs').addEventListener('keydown', event => handleTabKeys(event, componentTabs, tab => selectComponent(tab.dataset.component as Component, true)));
const narrow = matchMedia('(max-width: 600px)');
const orientComponents = () => element('.component-tabs').setAttribute('aria-orientation', narrow.matches ? 'horizontal' : 'vertical');
orientComponents();
narrow.addEventListener('change', orientComponents);

const commandTabs = Array.from(document.querySelectorAll<HTMLButtonElement>('[data-command]'));
let command: 'install' | 'replay' = 'install';
function selectCommand(id: 'install' | 'replay', focus = false) {
  command = id;
  for (const tab of commandTabs) {
    const selected = tab.dataset.command === id;
    tab.setAttribute('aria-selected', String(selected));
    tab.tabIndex = selected ? 0 : -1;
    if (selected && focus) tab.focus();
    element(`#${tab.dataset.command}-panel`).hidden = !selected;
  }
  element('.copy-command').setAttribute('aria-label', id === 'install' ? '复制获取项目命令' : '复制本地回放命令');
}
commandTabs.forEach(tab => tab.addEventListener('click', () => selectCommand(tab.dataset.command as typeof command)));
element('.command-tabs').addEventListener('keydown', event => handleTabKeys(event, commandTabs, tab => selectCommand(tab.dataset.command as typeof command, true)));
element('[data-next-command]').addEventListener('click', () => selectCommand('replay', true));

let toastTimer: ReturnType<typeof setTimeout>;
function toast(message: string) {
  const target = element('#toast');
  target.textContent = message;
  target.hidden = false;
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { target.hidden = true; }, 2600);
}
async function copy(text: string) {
  try {
    if (navigator.clipboard?.writeText) await navigator.clipboard.writeText(text);
    else {
      const field = document.createElement('textarea');
      field.value = text;
      field.style.cssText = 'position:fixed;left:-9999px;top:0';
      document.body.append(field);
      field.select();
      const copied = document.execCommand('copy');
      field.remove();
      if (!copied) throw new Error('Clipboard unavailable');
      element<HTMLButtonElement>('.copy-command').focus({ preventScroll: true });
    }
    toast('命令已复制');
  } catch {
    toast('未能复制，请在代码区选中命令后复制');
  }
}
element('.copy-command').addEventListener('click', () => void copy(element(`#${command}-panel code`).textContent ?? ''));

const menuButton = element<HTMLButtonElement>('.menu-toggle');
const mobileNav = element('#mobile-nav');
function setMenu(open: boolean, restoreFocus = false) {
  menuButton.setAttribute('aria-expanded', String(open));
  menuButton.setAttribute('aria-label', open ? '关闭导航' : '打开导航');
  mobileNav.hidden = !open;
  if (restoreFocus) menuButton.focus();
}
menuButton.addEventListener('click', () => setMenu(menuButton.getAttribute('aria-expanded') !== 'true'));
mobileNav.addEventListener('click', event => { if ((event.target as HTMLElement).closest('a')) setMenu(false); });
document.addEventListener('keydown', event => { if (event.key === 'Escape' && !mobileNav.hidden) setMenu(false, true); });
document.addEventListener('click', event => { if (!(event.target as HTMLElement).closest('.site-header') && !mobileNav.hidden) setMenu(false); });
const desktop = matchMedia('(min-width: 851px)');
desktop.addEventListener('change', () => { if (desktop.matches) setMenu(false); });

const reduceMotion = matchMedia('(prefers-reduced-motion: reduce)');
let paused = reduceMotion.matches;
function updateMotion() {
  document.documentElement.dataset.motion = paused ? 'paused' : 'running';
  const button = element('#motion-toggle');
  button.setAttribute('aria-pressed', String(paused));
  button.setAttribute('aria-label', paused ? '播放动效' : '暂停动效');
  button.innerHTML = `<i data-lucide="${paused ? 'play' : 'pause'}"></i><span>${paused ? '播放动效' : '暂停动效'}</span>`;
  icons();
}
updateMotion();
element('#motion-toggle').addEventListener('click', () => { paused = !paused; updateMotion(); });
reduceMotion.addEventListener('change', () => { paused = reduceMotion.matches; updateMotion(); });
