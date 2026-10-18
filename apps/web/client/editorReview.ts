import { compareSources, sourceChangeLocations, type SourceChangeLocation, type SourceComparison } from './sourceDiff';
import { sourceDiffRows } from './sourceDiffMarkup';
import type { SourceSelection } from './sourceText';

type EditorPosition = {
  start: number; end: number; direction: 'forward' | 'backward' | 'none'; top: number; left: number;
};

export class EditorReview {
  private editor: HTMLTextAreaElement;
  private baseline = '';
  private source = '';
  private active = false;
  private folded = true;
  private change = 0;
  private position: EditorPosition | undefined;
  private reading = { top: 0, left: 0 };
  private readonly comparisons = new Map<boolean, SourceComparison>();
  private rendered: SourceComparison | undefined;
  private locations = new Map<number, SourceChangeLocation>();
  private readonly view: HTMLElement;
  private readonly scroll: HTMLElement;
  private readonly toggle: HTMLButtonElement;

  constructor(private readonly dialog: HTMLDialogElement, private readonly closeTools: () => void,
    private readonly onPosition: () => void, private readonly onLocate: (position: SourceSelection) => void) {
    this.editor = this.control<HTMLTextAreaElement>('expanded-source');
    this.view = this.control('editor-review');
    this.scroll = this.control('editor-review-scroll');
    this.toggle = this.control<HTMLButtonElement>('editor-review-toggle');
    this.toggle.addEventListener('click', () => this.active ? this.close() : this.open());
    this.control<HTMLInputElement>('editor-review-fold').addEventListener('change', event => {
      this.folded = (event.target as HTMLInputElement).checked;
      const changeId = this.scroll.querySelector<HTMLElement>('.diff-change-current')?.dataset.changeStart;
      this.render();
      if (changeId !== undefined) {
        const changes = this.changes(), index = changes.findIndex(row => row.dataset.changeStart === changeId);
        if (index >= 0) this.change = index;
      }
      this.navigate(0, true);
    });
    this.control('editor-review-prev').addEventListener('click', () => this.navigate(-1, true));
    this.control('editor-review-next').addEventListener('click', () => this.navigate(1, true));
    this.control('editor-review-edit').addEventListener('click', () => this.editChange());
    this.dialog.addEventListener('keydown', event => {
      if (!this.active || event.isComposing) return;
      if (event.key === 'Escape') {
        event.preventDefault(); event.stopPropagation(); this.close();
      } else if ((event.ctrlKey || event.metaKey) && !event.altKey
        && ['f', 'g', 'h', 'z', 'y'].includes(event.key.toLowerCase())) {
        // Return shortcuts to the visible native buffer before navigation or undo runs.
        this.close();
      }
    }, true);
  }

  private control<T extends HTMLElement = HTMLElement>(id: string): T {
    return this.dialog.querySelector<T>(`#${id}`)!;
  }

  reset(editor: HTMLTextAreaElement, baseline: string) {
    this.active = false;
    this.editor = editor; this.baseline = baseline; this.source = editor.value;
    this.folded = true; this.change = 0; this.position = undefined; this.reading = { top: 0, left: 0 };
    this.comparisons.clear(); this.rendered = undefined;
    this.locations.clear();
    this.control('editor-review-target').hidden = true;
    this.control<HTMLButtonElement>('editor-review-edit').disabled = true;
    this.control('editor-review-body').replaceChildren();
    this.control<HTMLInputElement>('editor-review-fold').checked = true;
    this.showView();
  }

  updateSource() {
    if (this.source !== this.editor.value) {
      this.source = this.editor.value; this.comparisons.clear(); this.rendered = undefined;
      this.change = 0; this.reading = { top: 0, left: 0 };
      if (this.active) { this.render(); this.scroll.scrollTo(0, 0); }
    }
    this.toggle.hidden = !this.active && this.source === this.baseline;
  }

  private showView() {
    this.view.hidden = !this.active;
    this.control('editor-toolbar').hidden = this.active;
    this.control('editor-source-surface').hidden = this.active;
    this.toggle.hidden = !this.active && this.editor.value === this.baseline;
    this.toggle.setAttribute('aria-expanded', String(this.active));
    this.toggle.textContent = this.active ? '返回编辑' : '查看改动';
  }

  private open() {
    if (!this.dialog.open) return;
    this.updateSource();
    if (this.editor.value === this.baseline) return;
    // Closing find/replace first retains its selected match in the same textarea.
    this.closeTools();
    this.position = { start: this.editor.selectionStart, end: this.editor.selectionEnd,
      direction: this.editor.selectionDirection, top: this.editor.scrollTop, left: this.editor.scrollLeft };
    this.active = true; this.showView(); this.render();
    this.scroll.scrollTop = this.reading.top; this.scroll.scrollLeft = this.reading.left;
    (this.scroll.hidden ? this.control('editor-review-empty') : this.scroll).focus({ preventScroll: true });
  }

  close(): boolean {
    if (!this.active) return false;
    this.reading = { top: this.scroll.scrollTop, left: this.scroll.scrollLeft };
    this.active = false; this.showView();
    this.editor.focus({ preventScroll: true });
    if (this.position) {
      this.editor.setSelectionRange(this.position.start, this.position.end, this.position.direction);
      this.editor.scrollTop = this.position.top; this.editor.scrollLeft = this.position.left;
    }
    this.onPosition();
    return true;
  }

  private render() {
    let comparison = this.comparisons.get(this.folded);
    if (!comparison) {
      comparison = compareSources(this.baseline, this.source, this.folded);
      this.comparisons.set(this.folded, comparison);
    }
    if (this.rendered === comparison) return;
    this.rendered = comparison;
    const ready = comparison.status === 'ready', empty = this.control('editor-review-empty');
    this.control('editor-review-summary').hidden = !ready;
    this.control<HTMLLabelElement>('editor-review-fold-label').hidden = !ready;
    this.control('editor-review-navigation').hidden = !ready;
    this.scroll.hidden = !ready; empty.hidden = ready;
    const added = this.control('editor-review-added'), removed = this.control('editor-review-removed');
    added.textContent = `+${comparison.added}`; added.setAttribute('aria-label', `新增 ${comparison.added} 行`);
    removed.textContent = `-${comparison.removed}`; removed.setAttribute('aria-label', `删除 ${comparison.removed} 行`);
    empty.textContent = comparison.status === 'unavailable'
      ? '源码较大或差异过多，无法生成对比。返回编辑可查看完整源码。'
      : comparison.lineEndingsChanged ? '仅换行格式不同。' : '源码内容相同。';
    const notice = this.control('editor-review-notice');
    notice.hidden = !comparison.omittedLines;
    notice.textContent = comparison.omittedLines
      ? `另有 ${comparison.omittedLines.toLocaleString('zh-CN')} 行未展示；导航仅覆盖已展示的更改。返回编辑可查看完整源码。` : '';
    this.control('editor-review-body').innerHTML = ready ? sourceDiffRows(comparison.rows).markup : '';
    this.locations = ready ? sourceChangeLocations(this.source, comparison.rows) : new Map();
    this.navigate();
  }

  private editChange() {
    if (!this.active) return;
    // A changed native buffer must be reviewed again before using its old line target.
    if (this.editor.value !== this.source) { this.updateSource(); return; }
    const location = this.currentLocation();
    if (!location) return;
    this.close();
    this.onLocate({ start: location.offset, end: location.offset });
  }

  private currentLocation() {
    const row = this.changes()[this.change];
    return row ? this.locations.get(Number(row.dataset.changeStart)) : undefined;
  }

  private changes() {
    return Array.from(this.scroll.querySelectorAll<HTMLElement>('[data-change-start]'));
  }

  private navigate(move = 0, align = false) {
    const changes = this.changes();
    this.change = Math.max(0, Math.min(this.change + move, changes.length - 1));
    this.control<HTMLButtonElement>('editor-review-prev').disabled = !changes.length || this.change === 0;
    this.control<HTMLButtonElement>('editor-review-next').disabled = this.change >= changes.length - 1;
    this.control('editor-review-position').textContent = `${changes.length ? this.change + 1 : 0}/${changes.length}`;
    const location = this.currentLocation();
    this.control('editor-review-target').hidden = !location;
    this.control<HTMLButtonElement>('editor-review-edit').disabled = !location;
    this.control('editor-review-location').textContent = location ? `当前源码 · 第 ${location.line} 行` : '';
    changes.forEach((row, index) => row.classList.toggle('diff-change-current', index === this.change));
    if (align && changes[this.change]) {
      const headerHeight = this.scroll.querySelector('thead')?.getBoundingClientRect().height ?? 0;
      this.scroll.scrollTop += changes[this.change].getBoundingClientRect().top - this.scroll.getBoundingClientRect().top - headerHeight;
    }
  }
}
