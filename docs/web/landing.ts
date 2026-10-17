import {
  createIcons, ArrowDown, ArrowDownRight, ArrowRight, ArrowUpRight, Blocks, Check, ChevronLeft, ChevronRight, Code2,
  Copy, Download, ExternalLink, FileCode2, FileJson2, Files, GitFork, Globe, History, Info,
  Maximize2, Menu, Pause, Play, Plus, RotateCcw, ScanLine, ShieldCheck, Terminal, X, ZoomIn, ZoomOut,
} from 'lucide';
import { gsap } from 'gsap';
import { createSelectionIndicator } from './selectionIndicator';

const iconSet = { ArrowDown, ArrowDownRight, ArrowRight, ArrowUpRight, Blocks, Check, ChevronLeft, ChevronRight, Code2, Copy,
  Download, ExternalLink, FileCode2, FileJson2, Files, GitFork, Globe, History, Info, Maximize2, Menu, Pause, Play, Plus,
  RotateCcw, ScanLine, ShieldCheck, Terminal, X, ZoomIn, ZoomOut };
const icons = () => createIcons({ icons: iconSet, attrs: { 'aria-hidden': 'true' } });
const element = <T extends HTMLElement = HTMLElement>(selector: string): T => {
  const result = document.querySelector<T>(selector);
  if (!result) throw new Error(`Missing landing page element: ${selector}`);
  return result;
};
icons();
document.documentElement.classList.add('js');
const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)');
const selectionTargets = new Set<Element>();
function animateSelection(targets: Element[], distance = 7) {
  for (const target of targets) selectionTargets.add(target);
  gsap.killTweensOf(targets);
  if (reducedMotion.matches) {
    gsap.set(targets, { clearProps: 'opacity,transform' });
    return;
  }
  gsap.set(targets, { opacity: .45, y: distance });
  gsap.to(targets, {
    opacity: 1, y: 0, duration: .28, stagger: .035, ease: 'power2.out', clearProps: 'opacity,transform',
  });
}

let introPlayed = false;
const revealed = new WeakSet<Element>();
const entranceMotion = gsap.matchMedia();
entranceMotion.add('(prefers-reduced-motion: no-preference)', context => {
  if (!introPlayed) {
    introPlayed = true;
    gsap.set('.hero-name', { yPercent: 110 });
    gsap.set('.hero-category, .hero-description', { opacity: 0, y: 12 });
    gsap.set('.hero-actions', { opacity: 0, y: 10 });
    gsap.set('.workbench-preview', { opacity: 0, y: 20 });
    gsap.timeline({ defaults: { duration: .65, ease: 'power3.out', clearProps: 'opacity,transform' } })
      .to('.hero-name', { yPercent: 0, duration: .85 }, 0)
      .to('.hero-category, .hero-description', { opacity: 1, y: 0, stagger: .06 }, .16)
      .to('.hero-actions', { opacity: 1, y: 0 }, .28)
      .to('.workbench-preview', { opacity: 1, y: 0, duration: .8 }, .32);
  }
  const observer = new IntersectionObserver(entries => {
    for (const entry of entries) {
      if (!entry.isIntersecting || revealed.has(entry.target)) continue;
      revealed.add(entry.target);
      observer.unobserve(entry.target);
      context.add(() => {
        const target = entry.target;
        const settle = { duration: .6, ease: 'power2.out', clearProps: 'opacity,transform' };
        if (target.matches('.proof-row')) {
          gsap.fromTo(target.children, { opacity: .4, x: 16 }, { ...settle, opacity: 1, x: 0, stagger: .06 });
        } else if (target.matches('.component-explorer')) {
          gsap.fromTo(target.querySelectorAll('.component-tab'), { opacity: .35, x: -20 },
            { ...settle, opacity: 1, x: 0, stagger: .07 });
          gsap.fromTo(target.querySelector('.component-panel'), { opacity: .4, y: 16 },
            { ...settle, opacity: 1, y: 0, delay: .2 });
        } else if (target.matches('.product-fragment, .archive-showcase')) {
          gsap.fromTo(target.querySelector('img'), { opacity: .5, scale: .98 },
            { ...settle, opacity: 1, scale: 1, duration: .8 });
          gsap.fromTo(target.querySelector('figcaption'), { opacity: .4, y: 12 },
            { ...settle, opacity: 1, y: 0, delay: .15 });
        } else if (target.matches('.faq-list')) {
          gsap.fromTo(target.children, { opacity: .4, x: 20 },
            { ...settle, opacity: 1, x: 0, stagger: .08 });
        } else if (target.matches('.section-heading, .record-notes, .start-copy')) {
          gsap.fromTo(target.children, { opacity: .4, y: 18 },
            { ...settle, opacity: 1, y: 0, stagger: .08 });
        } else {
          gsap.fromTo(target, { opacity: .4, y: 20 }, { ...settle, opacity: 1, y: 0 });
        }
      });
    }
  }, { rootMargin: '0px 0px -35px 0px', threshold: .08 });
  document.querySelectorAll('.section-heading, .replay-window, .proof-row, .component-explorer, .product-fragment, .archive-showcase, .record-notes, .start-copy, .start-terminal, .faq-list')
    .forEach(target => observer.observe(target));
  return () => observer.disconnect();
});

const components = {
  m1: { contract: 'M1 · 证明构造接口', title: '把想法，写成候选证明。',
    description: '调用模型会话，在隔离工作区中构造和修复 Lean 候选。研究你的生成方式、提示和修复策略。',
    input: '题目 · 上下文 · 操作 · 模型会话', output: '候选记录 · 工作区中的证明' },
  m2: { contract: 'M2 · 检查反馈接口', title: '让诊断，成为研究线索。',
    description: '检查候选与辅助证明，把 Lean 诊断交还研究过程。局部检查之后，集成结果仍需接受完整原题的独立验收。',
    input: '固定题目 · 候选源码 · 检查环境', output: '绑定源码摘要的检查与诊断' },
  m3: { contract: 'M3 · 搜索接口', title: '让下一步，有章可循。',
    description: '选择就绪任务，决定继续、重试或停止。把任务排序与路线、预算约束放在一起研究。',
    input: '研究状态 · 候选操作 · 共享预算', output: '下一步操作 · 有序就绪任务' },
  m4: { contract: 'M4 · 上下文接口', title: '把相关证据，带入思考。',
    description: '从题目、已有成果与失败记录中整理上下文。比较信息选择、上下文压缩和检索策略。',
    input: '题目 · 当前任务 · 可见证据', output: '带来源身份的上下文包' },
  m5: { contract: 'M5 · 协作复用接口', title: '让分工与交接，可以研究。',
    description: '组织隔离工作区、任务分配与独立审阅。比较单 Agent、独立并行与任务协作的研究方法。',
    input: '就绪任务 · Worker · 路线约束', output: '工作区配置 · 任务与审阅分配' },
};
type Component = keyof typeof components;
const narrow = matchMedia('(max-width: 600px)');
const componentTabs = Array.from(document.querySelectorAll<HTMLButtonElement>('[data-component]'));
const componentIndicator = createSelectionIndicator(element('.component-tabs'), reducedMotion);
function selectComponent(id: Component, focus = false) {
  const content = components[id];
  if (!content) return;
  const changed = element('#component-panel').getAttribute('aria-labelledby') !== `tab-${id}`;
  for (const tab of componentTabs) {
    const selected = tab.dataset.component === id;
    tab.setAttribute('aria-selected', String(selected));
    tab.tabIndex = selected ? 0 : -1;
    if (selected && focus) tab.focus();
  }
  element('#component-panel').setAttribute('aria-labelledby', `tab-${id}`);
  for (const [key, value] of Object.entries({ kicker: content.contract, title: content.title,
    description: content.description, input: content.input, output: content.output })) {
    element(`#module-${key}`).textContent = value;
  }
  componentIndicator.update();
  if (changed) animateSelection([element('.module-details')]);
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
const replayIndicator = createSelectionIndicator(element('.replay-tabs'), reducedMotion);
const replayWindow = element('.replay-window');
const replayPanels = replayTabs.map(tab => element(`#stage-${tab.dataset.replayStage}`));
const replayPlay = element<HTMLButtonElement>('#replay-play');
const replayProgress = element('#replay-progress');
const replayFill = element('.replay-progress-fill');
const replayLabels = ['候选证明', 'Lean 反馈', '修复候选', '完整原题验收'];
const replayDurations = [3.2, 4.4, 3.6, 4];
let replayIndex = replayTabs.length - 1;
let replayPlaying = false;
let replayStarted = false;
let replayComplete = false;
let replayInView = false;
let replayClock: gsap.core.Timeline | undefined;
element('.replay-playback').hidden = false;

function updateReplayControls() {
  replayWindow.dataset.replayPlaying = String(replayPlaying);
  replayWindow.dataset.replayCurrent = replayTabs[replayIndex].dataset.replayStage;
  replayWindow.dataset.replayState = replayPlaying ? 'playing' : replayComplete ? 'complete' : 'paused';
  const label = replayPlaying ? '暂停回放' : replayStarted ? '继续播放' : '播放预设回放';
  replayPlay.setAttribute('aria-label', label);
  replayPlay.title = label;
  replayPlay.setAttribute('aria-pressed', String(replayPlaying));
  element<HTMLButtonElement>('#replay-prev').disabled = replayIndex === 0;
  element<HTMLButtonElement>('#replay-next').disabled = replayIndex === replayTabs.length - 1;
  element('#replay-step-number').textContent = `0${replayIndex + 1} / 04`;
  element('#replay-step-label').textContent = replayLabels[replayIndex];
  const status = replayPlaying ? '播放中' : replayComplete ? '回放结束' : '已暂停';
  if (element('#replay-status').textContent !== status) element('#replay-status').textContent = status;
  replayProgress.setAttribute('aria-valuenow', String(replayIndex + 1));
  replayProgress.setAttribute('aria-valuetext', `第 ${replayIndex + 1} 步，共 4 步：${replayLabels[replayIndex]}`);
}
function renderReplayStage(index: number, focus = false) {
  const changed = replayIndex !== index;
  replayIndex = index;
  for (const [position, stage] of replayTabs.entries()) {
    const selected = position === index;
    stage.setAttribute('aria-selected', String(selected));
    stage.tabIndex = selected ? 0 : -1;
    stage.dataset.stepState = position < index ? 'complete' : selected ? 'current' : 'upcoming';
    replayPanels[position].hidden = !selected;
  }
  gsap.set(replayFill, { scaleX: (index + 1) / replayTabs.length });
  replayIndicator.update();
  updateReplayControls();
  if (changed) animateSelection([replayPanels[index]], 6);
  if (focus) replayTabs[index].focus({ preventScroll: true });
}
function pauseReplay() {
  replayClock?.pause();
  replayPlaying = false;
  updateReplayControls();
}
function selectReplayStage(tab: HTMLButtonElement, focus = false) {
  pauseReplay();
  replayClock?.kill();
  replayClock = undefined;
  replayStarted = false;
  replayComplete = false;
  renderReplayStage(replayTabs.indexOf(tab), focus);
}
function scheduleReplayStage() {
  replayClock?.kill();
  replayClock = gsap.timeline({ onComplete: () => {
    replayClock = undefined;
    if (!replayPlaying) return;
    if (replayIndex === replayTabs.length - 1) {
      replayPlaying = false;
      replayStarted = false;
      replayComplete = true;
      updateReplayControls();
      return;
    }
    renderReplayStage(replayIndex + 1);
    scheduleReplayStage();
  } });
  if (reducedMotion.matches) replayClock.to({}, { duration: replayDurations[replayIndex] });
  else replayClock.fromTo(replayFill, { scaleX: replayIndex / replayTabs.length }, {
    scaleX: (replayIndex + 1) / replayTabs.length, duration: replayDurations[replayIndex], ease: 'none',
  });
}
function playReplay(restart = false) {
  if (document.hidden || !replayInView) return;
  if (restart || !replayStarted) {
    replayClock?.kill();
    replayClock = undefined;
    replayComplete = false;
    renderReplayStage(0);
  }
  replayStarted = true;
  replayPlaying = true;
  updateReplayControls();
  if (replayClock) replayClock.resume();
  else scheduleReplayStage();
}
replayTabs.forEach(tab => tab.addEventListener('click', () => selectReplayStage(tab)));
element('.replay-tabs').addEventListener('keydown', event => handleTabKeys(event, replayTabs, tab => selectReplayStage(tab, true)));
replayPlay.addEventListener('click', () => { if (replayPlaying) pauseReplay(); else playReplay(); });
element('#replay-prev').addEventListener('click', () => selectReplayStage(replayTabs[Math.max(0, replayIndex - 1)]));
element('#replay-next').addEventListener('click', () => selectReplayStage(replayTabs[Math.min(replayTabs.length - 1, replayIndex + 1)]));
element('#replay-restart').addEventListener('click', () => playReplay(true));
const replayVisibility = new IntersectionObserver(entries => {
  replayInView = entries[0].isIntersecting && entries[0].intersectionRect.height > 0;
  if (!replayInView && replayPlaying) pauseReplay();
}, { rootMargin: '-70px 0px 0px 0px' });
replayVisibility.observe(replayWindow);
document.addEventListener('visibilitychange', () => { if (document.hidden && replayPlaying) pauseReplay(); });
window.addEventListener('pagehide', pauseReplay);
reducedMotion.addEventListener('change', () => {
  pauseReplay();
  replayClock?.kill();
  replayClock = undefined;
  if (selectionTargets.size) {
    gsap.killTweensOf([...selectionTargets]);
    gsap.set([...selectionTargets], { clearProps: 'opacity,transform' });
  }
  gsap.set(replayFill, { scaleX: (replayIndex + 1) / replayTabs.length });
});
updateReplayControls();

element('.component-tabs').addEventListener('keydown', event => handleTabKeys(event, componentTabs, tab => selectComponent(tab.dataset.component as Component, true)));
const componentGrid = matchMedia('(max-width: 900px)');
const orientComponents = () => {
  element('.component-tabs').setAttribute('aria-orientation', componentGrid.matches ? 'horizontal' : 'vertical');
};
orientComponents();
componentGrid.addEventListener('change', orientComponents);

const previewLink = element<HTMLAnchorElement>('.workbench-image-link');
const previewDialog = element<HTMLDialogElement>('#workbench-dialog');
const previewMedia = element('.preview-dialog-media');
const previewZoom = element<HTMLButtonElement>('.preview-zoom');
const updatePreviewSource = () => {
  const source = `assets/workbench-full-${narrow.matches ? 'mobile' : 'desktop'}.png`;
  previewLink.href = source;
  element<HTMLAnchorElement>('.preview-original').href = source;
};
updatePreviewSource();
narrow.addEventListener('change', updatePreviewSource);
function zoomPreview(zoomed: boolean) {
  const factor = zoomed ? 2 : .5;
  const left = (previewMedia.scrollLeft + previewMedia.clientWidth / 2) * factor - previewMedia.clientWidth / 2;
  const top = (previewMedia.scrollTop + previewMedia.clientHeight / 2) * factor - previewMedia.clientHeight / 2;
  previewMedia.classList.toggle('is-zoomed', zoomed);
  previewZoom.setAttribute('aria-pressed', String(zoomed));
  previewZoom.setAttribute('aria-label', zoomed ? '适应窗口' : '放大截图');
  previewZoom.title = zoomed ? '适应窗口' : '放大截图';
  previewMedia.scrollTo({ left: zoomed ? left : 0, top: zoomed ? top : 0 });
}
previewLink.addEventListener('click', event => {
  if (!previewDialog.showModal || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
  event.preventDefault();
  zoomPreview(false);
  previewDialog.showModal();
  previewMedia.scrollTo({ left: 0, top: 0 });
  document.documentElement.classList.add('preview-open');
});
previewZoom.addEventListener('click', () => zoomPreview(previewZoom.getAttribute('aria-pressed') !== 'true'));
element('.preview-close').addEventListener('click', () => previewDialog.close());
previewDialog.addEventListener('close', () => document.documentElement.classList.remove('preview-open'));
previewDialog.addEventListener('click', event => {
  if (event.target !== previewDialog) return;
  const bounds = previewDialog.getBoundingClientRect();
  if (event.clientX < bounds.left || event.clientX > bounds.right || event.clientY < bounds.top || event.clientY > bounds.bottom) previewDialog.close();
});
let pan: { pointer: number; x: number; y: number; left: number; top: number } | undefined;
previewMedia.addEventListener('pointerdown', event => {
  if (event.pointerType !== 'mouse' || event.button !== 0 || !previewMedia.classList.contains('is-zoomed')) return;
  event.preventDefault();
  pan = { pointer: event.pointerId, x: event.clientX, y: event.clientY, left: previewMedia.scrollLeft, top: previewMedia.scrollTop };
  previewMedia.setPointerCapture(event.pointerId);
  previewMedia.classList.add('is-panning');
});
previewMedia.addEventListener('pointermove', event => {
  if (!pan || pan.pointer !== event.pointerId) return;
  previewMedia.scrollLeft = pan.left + pan.x - event.clientX;
  previewMedia.scrollTop = pan.top + pan.y - event.clientY;
});
previewMedia.addEventListener('pointerup', event => {
  if (previewMedia.hasPointerCapture(event.pointerId)) previewMedia.releasePointerCapture(event.pointerId);
});
previewMedia.addEventListener('lostpointercapture', () => {
  pan = undefined;
  previewMedia.classList.remove('is-panning');
});

const commandTabs = Array.from(document.querySelectorAll<HTMLButtonElement>('[data-command]'));
const commandIndicator = createSelectionIndicator(element('.command-tabs'), reducedMotion);
type Command = 'workbench' | 'install' | 'replay';
const commandLabels: Record<Command, string> = {
  workbench: '复制部署工作台命令', install: '复制获取项目命令', replay: '复制本地回放命令',
};
let command: Command = 'workbench';
function selectCommand(id: Command, focus = false) {
  const changed = command !== id;
  command = id;
  for (const tab of commandTabs) {
    const selected = tab.dataset.command === id;
    tab.setAttribute('aria-selected', String(selected));
    tab.tabIndex = selected ? 0 : -1;
    if (selected && focus) tab.focus();
    element(`#${tab.dataset.command}-panel`).hidden = !selected;
  }
  element('.copy-command').setAttribute('aria-label', commandLabels[id]);
  commandIndicator.update();
  if (changed) animateSelection([element(`#${id}-panel`)], 5);
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
const desktop = matchMedia('(min-width: 901px)');
desktop.addEventListener('change', () => { if (desktop.matches) setMenu(false); });
const indicators = [componentIndicator, replayIndicator, commandIndicator];
document.addEventListener('visibilitychange', () => {
  if (document.hidden) indicators.forEach(indicator => indicator.update(false));
});
window.addEventListener('pagehide', event => indicators.forEach(indicator => {
  if (event.persisted) indicator.update(false);
  else indicator.destroy();
}));
window.addEventListener('pageshow', () => indicators.forEach(indicator => indicator.update(false)));
document.documentElement.dataset.landingReady = 'true';
