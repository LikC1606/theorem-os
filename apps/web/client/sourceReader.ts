import { findSourceMatches, leanTokens, type SourceMatch } from './sourceText';

type Surface = { id: string; code: HTMLElement; scroll: HTMLElement; toolbar: HTMLElement; scope?: string };
const tokenKinds = ['comment', 'keyword', 'tactic', 'placeholder', 'string', 'number'] as const;
const canHighlight = () => typeof CSS !== 'undefined' && Boolean(CSS.highlights) && typeof Highlight !== 'undefined';
const markup = `<div class="source-reader-tools"><span id="source-find-location" class="mono"></span><button type="button" id="open-source-find" class="source-find-toggle" aria-expanded="false" aria-controls="source-find-controls" title="在源码中查找（Ctrl / ⌘ F）"><i data-lucide="search"></i>查找源码</button></div>
  <div class="source-find" id="source-find-controls" hidden>
    <div class="source-find-entry"><label for="source-find-input" class="sr-only">查找源码文本</label><input type="search" id="source-find-input" placeholder="查找文本…" maxlength="256" autocomplete="off" spellcheck="false" aria-describedby="source-find-position source-find-location source-find-scope"><span id="source-find-position" class="mono" role="status" aria-atomic="true">0/0</span></div>
    <div class="source-find-actions"><button type="button" id="source-find-case" class="icon-button source-find-case" aria-label="区分大小写" title="区分大小写" aria-pressed="false">Aa</button><button type="button" id="source-find-prev" class="icon-button" aria-label="上一个匹配" title="上一个匹配（Shift+Enter）"><i data-lucide="chevron-up"></i></button><button type="button" id="source-find-next" class="icon-button" aria-label="下一个匹配" title="下一个匹配（Enter）"><i data-lucide="chevron-down"></i></button><button type="button" id="close-source-find" class="icon-button" aria-label="关闭源码查找" title="关闭源码查找（Esc）"><i data-lucide="x"></i></button></div>
  </div><p id="source-find-scope" class="source-find-scope" hidden></p>`;

export class SourceReader {
  private surface?: Surface;
  private identity = '';
  private node?: Text;
  private text = '';
  private opened = false;
  private query = '';
  private caseSensitive = false;
  private matches: SourceMatch[] = [];
  private truncated = false;
  private index = 0;
  private searchSignature = '';

  constructor(private readonly hydrate: (root: HTMLElement) => void, private readonly expandDraft: () => void) {}

  update(surface?: Surface) {
    if (!surface) {
      this.surface = undefined; this.node = undefined;
      this.clearHighlights();
      return;
    }
    if (this.identity !== surface.id) {
      this.identity = surface.id;
      this.opened = false; this.query = ''; this.caseSensitive = false; this.index = 0;
      this.searchSignature = '';
    }
    this.surface = surface;
    if (!surface.toolbar.hasChildNodes()) this.mount(surface.toolbar);
    const node = surface.code.firstChild;
    const source = surface.code.textContent ?? '';
    if (node !== this.node || source !== this.text) {
      this.node = node instanceof Text ? node : undefined;
      this.text = source;
      this.searchSignature = '';
      this.paintSyntax();
    }
    this.refresh();
  }

  private mount(toolbar: HTMLElement) {
    toolbar.innerHTML = markup;
    this.hydrate(toolbar);
    toolbar.addEventListener('input', event => {
      if ((event.target as HTMLElement).id !== 'source-find-input') return;
      this.query = (event.target as HTMLInputElement).value;
      this.index = 0; this.refresh(); this.reveal();
    });
    toolbar.addEventListener('click', event => {
      const id = (event.target as Element).closest('button')?.id;
      if (id === 'open-source-find') this.opened ? this.close() : this.open();
      if (id === 'close-source-find') this.close();
      if (id === 'source-find-next') this.navigate(1);
      if (id === 'source-find-prev') this.navigate(-1);
      if (id === 'source-find-case') {
        this.caseSensitive = !this.caseSensitive;
        this.index = 0; this.refresh(); this.reveal();
      }
    });
  }

  handleKeydown(event: KeyboardEvent): boolean {
    const surface = this.surface, target = event.target;
    if (!surface || !(target instanceof Node) || document.querySelector('dialog[open]') || event.isComposing
      || (!surface.scroll.contains(target) && !surface.toolbar.contains(target))) return false;
    if ((event.ctrlKey || event.metaKey) && !event.altKey && event.key.toLowerCase() === 'f') {
      event.preventDefault(); this.open(); return true;
    }
    if (this.opened && surface.toolbar.contains(target) && event.key === 'Escape') {
      event.preventDefault(); this.close(); return true;
    }
    if (this.opened && target === surface.toolbar.querySelector('#source-find-input') && event.key === 'Enter') {
      event.preventDefault(); this.navigate(event.shiftKey ? -1 : 1); return true;
    }
    return false;
  }

  private open() {
    this.opened = true;
    this.expandDraft();
    this.refresh();
    const input = this.surface?.toolbar.querySelector<HTMLInputElement>('#source-find-input');
    input?.focus({ preventScroll: true }); input?.select();
  }

  private close() {
    this.opened = false;
    this.refresh();
    this.surface?.scroll.focus({ preventScroll: true });
  }

  private refresh() {
    const surface = this.surface;
    if (!surface) return;
    const signature = JSON.stringify([this.text, this.query, this.caseSensitive, this.opened]);
    if (signature !== this.searchSignature) {
      this.searchSignature = signature;
      const result = findSourceMatches(this.text, this.opened ? this.query : '', this.caseSensitive);
      this.matches = result.matches; this.truncated = result.truncated;
      this.index = Math.max(0, Math.min(this.index, this.matches.length - 1));
      this.paintMatches();
    }
    this.renderControls();
  }

  private renderControls() {
    const toolbar = this.surface!.toolbar;
    const text = (selector: string, value: string) => {
      const target = toolbar.querySelector(selector)!;
      if (target.textContent !== value) target.textContent = value;
    };
    const controls = toolbar.querySelector<HTMLElement>('.source-find')!;
    if (controls.hidden === this.opened) controls.hidden = !this.opened;
    const toggle = toolbar.querySelector('#open-source-find')!;
    if (toggle.getAttribute('aria-expanded') !== String(this.opened)) toggle.setAttribute('aria-expanded', String(this.opened));
    const input = toolbar.querySelector<HTMLInputElement>('#source-find-input')!;
    if (input.value !== this.query) input.value = this.query;
    const caseButton = toolbar.querySelector('#source-find-case')!;
    if (caseButton.getAttribute('aria-pressed') !== String(this.caseSensitive)) caseButton.setAttribute('aria-pressed', String(this.caseSensitive));
    for (const id of ['source-find-prev', 'source-find-next']) {
      const button = toolbar.querySelector<HTMLButtonElement>(`#${id}`)!;
      if (button.disabled !== !this.matches.length) button.disabled = !this.matches.length;
    }
    text('#source-find-position', `${this.matches.length ? this.index + 1 : 0}/${this.matches.length}${this.truncated ? '+' : ''}`);
    const match = this.matches[this.index];
    text('#source-find-location', this.opened && match ? `第 ${match.line} 行 · 第 ${match.column} 列` : '');
    const scope = toolbar.querySelector<HTMLElement>('#source-find-scope')!;
    text('#source-find-scope', this.surface!.scope ?? '');
    const showScope = this.opened && Boolean(this.surface!.scope);
    if (scope.hidden === showScope) scope.hidden = !showScope;
  }

  private range(start: number, end: number) {
    if (!this.node) return undefined;
    const range = document.createRange();
    range.setStart(this.node, start); range.setEnd(this.node, end);
    return range;
  }

  private clearHighlights() {
    if (!canHighlight()) return;
    for (const key of [...tokenKinds.map(kind => `lean-${kind}`), 'source-matches', 'source-current']) CSS.highlights.delete(key);
  }

  private paintSyntax() {
    if (!canHighlight()) return;
    const groups = new Map(tokenKinds.map(kind => [kind, new Highlight()]));
    for (const token of leanTokens(this.text)) {
      const range = this.range(token.start, token.end);
      if (range) groups.get(token.kind)!.add(range);
    }
    for (const [kind, highlight] of groups) CSS.highlights.set(`lean-${kind}`, highlight);
  }

  private paintMatches() {
    if (!canHighlight()) return;
    const matches = new Highlight(), active = new Highlight();
    matches.priority = 1; active.priority = 2;
    for (const [index, match] of this.matches.entries()) {
      const range = this.range(match.start, match.end);
      if (range) { matches.add(range); if (index === this.index) active.add(range); }
    }
    CSS.highlights.set('source-matches', matches); CSS.highlights.set('source-current', active);
  }

  private navigate(direction: number) {
    if (!this.matches.length) return;
    this.index = (this.index + direction + this.matches.length) % this.matches.length;
    this.paintMatches(); this.renderControls(); this.reveal();
  }

  private reveal() {
    const match = this.matches[this.index], surface = this.surface;
    if (!surface || !match) return;
    const range = this.range(match.start, match.end);
    const rect = range?.getClientRects()[0];
    if (!rect) return;
    const bounds = surface.scroll.getBoundingClientRect();
    const gutter = surface.scroll.querySelector('.source-line-numbers,.preview-line-numbers')?.getBoundingClientRect().width ?? 0;
    const width = surface.scroll.clientWidth - gutter;
    surface.scroll.scrollTo({
      top: surface.scroll.scrollTop + rect.top - bounds.top - Math.max(0, (surface.scroll.clientHeight - rect.height) / 2),
      left: surface.scroll.scrollLeft + rect.left - bounds.left - gutter - Math.max(8, (width - rect.width) / 2),
      behavior: 'instant',
    });
  }
}
