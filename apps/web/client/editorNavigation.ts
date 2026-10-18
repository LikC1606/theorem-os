import { findSourceMatches, type SourceMatch, type SourceSelection } from './sourceText';
import { sourceReplaceEdit } from './sourceReplace';

// Measure the native textarea's wrapping without changing its value or undo stack.
function measureRange(editor: HTMLTextAreaElement, start: number, end = start) {
  const style = getComputedStyle(editor), mirror = document.createElement('div');
  for (const property of ['font-family', 'font-size', 'font-weight', 'font-style', 'font-variant', 'font-stretch',
    'line-height', 'letter-spacing', 'word-spacing', 'tab-size', 'text-align', 'text-indent', 'text-transform',
    'word-break', 'direction', 'padding-top', 'padding-right', 'padding-bottom', 'padding-left']) {
    mirror.style.setProperty(property, style.getPropertyValue(property));
  }
  Object.assign(mirror.style, { position: 'fixed', top: '0', left: '0', visibility: 'hidden', pointerEvents: 'none',
    boxSizing: 'border-box', width: `${editor.clientWidth}px`, whiteSpace: editor.wrap === 'off' ? 'pre' : 'pre-wrap',
    overflowWrap: editor.wrap === 'off' ? 'normal' : 'break-word' });
  mirror.setAttribute('aria-hidden', 'true');
  // A sentinel gives the caret a measurable position on a trailing blank line.
  const text = document.createTextNode(`${editor.value}\u200b`);
  mirror.append(text); document.body.append(mirror);
  try {
    const range = document.createRange();
    range.setStart(text, start); range.setEnd(text, end);
    let rectangles = Array.from(range.getClientRects());
    if (!rectangles.some(rect => rect.height)) {
      // Collapsed ranges on internal blank lines have no box in Chromium.
      text.insertData(start, '\u200b');
      range.setStart(text, start); range.setEnd(text, start + 1);
      rectangles = Array.from(range.getClientRects());
    }
    const box = mirror.getBoundingClientRect();
    return rectangles.filter(rect => rect.height).map(rect => ({ top: rect.top - box.top, left: rect.left - box.left,
      width: rect.width, height: rect.height }));
  } finally { mirror.remove(); }
}

function revealOffset(editor: HTMLTextAreaElement, offset: number) {
  const caret = measureRange(editor, offset)[0];
  if (!caret) return;
  editor.scrollTo({ top: caret.top - Math.max(0, (editor.clientHeight - caret.height) / 2),
    left: editor.wrap === 'off' ? caret.left - editor.clientWidth / 2 : 0, behavior: 'instant' });
}

export class EditorNavigation {
  private mode: 'find' | 'line' | undefined;
  private source = '';
  private lineStarts = [0];
  private matches: SourceMatch[] = [];
  private truncated = false;
  private caseSensitive = false;
  private lineError = '';
  private replaceOpened = false;
  private replaceMessage = '';
  private replaceError = false;
  private composing = false;
  private paintFrame = 0;
  private editor: HTMLTextAreaElement;
  private readonly resizeObserver: ResizeObserver;
  private readonly query: HTMLInputElement;
  private readonly line: HTMLInputElement;
  private readonly replacement: HTMLInputElement;

  constructor(private readonly dialog: HTMLDialogElement, private readonly onPosition: () => void,
    private readonly onEdit: () => void, private readonly sourceLimit: () => number) {
    this.editor = this.control<HTMLTextAreaElement>('expanded-source');
    this.query = this.control<HTMLInputElement>('editor-find-input');
    this.line = this.control<HTMLInputElement>('editor-line-input');
    this.replacement = this.control<HTMLInputElement>('editor-replace-input');
    for (const mode of ['find', 'line'] as const) {
      this.control(`editor-${mode}-toggle`).addEventListener('click', () => this.mode === mode ? this.close() : this.open(mode));
      this.control(`editor-${mode}-close`).addEventListener('click', () => this.close());
    }
    this.query.addEventListener('input', event => {
      this.replaceMessage = '';
      this.search();
      if (!(event as InputEvent).isComposing) this.nearest();
    });
    this.replacement.addEventListener('input', () => { this.replaceMessage = ''; this.render(); });
    for (const input of [this.query, this.replacement]) {
      input.addEventListener('compositionstart', () => { this.composing = true; this.render(); });
      input.addEventListener('compositionend', () => {
        this.composing = false;
        this.search();
        if (input === this.query) this.nearest();
      });
    }
    this.line.addEventListener('input', () => { this.lineError = ''; this.render(); });
    this.control('editor-find-case').addEventListener('click', () => {
      this.replaceMessage = '';
      this.caseSensitive = !this.caseSensitive; this.search(); this.nearest();
    });
    this.control('editor-find-prev').addEventListener('click', () => this.navigate(-1));
    this.control('editor-find-next').addEventListener('click', () => this.navigate(1));
    this.control('editor-line-go').addEventListener('click', () => this.jump());
    this.control('editor-replace-toggle').addEventListener('click', () => {
      if (this.replaceOpened) {
        this.replaceOpened = false; this.replaceMessage = ''; this.render();
        this.query.focus({ preventScroll: true });
      } else this.openReplace();
    });
    this.control('editor-replace-one').addEventListener('click', () => this.replace(false));
    this.control('editor-replace-all').addEventListener('click', () => this.replace(true));
    this.dialog.addEventListener('scroll', event => {
      if (event.target === this.editor) this.queueHighlight();
    }, true);
    this.dialog.addEventListener('focusin', () => this.queueHighlight());
    this.dialog.addEventListener('close', () => this.queueHighlight());
    this.resizeObserver = new ResizeObserver(() => this.queueHighlight());
    this.resizeObserver.observe(this.editor);
    this.dialog.addEventListener('keydown', event => {
      if (event.isComposing || this.composing) return;
      if ((event.ctrlKey || event.metaKey) && !event.altKey && !event.shiftKey && ['f', 'g', 'h'].includes(event.key.toLowerCase())) {
        event.preventDefault();
        if (event.key.toLowerCase() === 'h') this.openReplace();
        else this.open(event.key.toLowerCase() === 'f' ? 'find' : 'line');
      } else if (event.key === 'Escape' && this.mode) {
        event.preventDefault(); event.stopPropagation(); this.close();
      } else if (event.key === 'Enter' && !event.ctrlKey && !event.metaKey && !event.altKey) {
        if (event.target === this.query) { event.preventDefault(); this.navigate(event.shiftKey ? -1 : 1); }
        if (event.target === this.line) { event.preventDefault(); this.jump(); }
        if (event.target === this.replacement && !event.shiftKey) { event.preventDefault(); this.replace(false); }
      }
    });
  }

  private control<T extends HTMLElement = HTMLElement>(id: string): T {
    return this.dialog.querySelector<T>(`#${id}`)!;
  }

  reset(editor: HTMLTextAreaElement) {
    if (this.editor !== editor) {
      this.resizeObserver.unobserve(this.editor);
      this.editor = editor;
      this.resizeObserver.observe(editor);
    }
    this.mode = undefined; this.query.value = ''; this.line.value = '1';
    this.caseSensitive = false; this.lineError = '';
    this.replaceOpened = false; this.replacement.value = ''; this.replaceMessage = ''; this.replaceError = false; this.composing = false;
    this.updateSource();
  }

  updateSource() {
    if (this.source !== this.editor.value) this.replaceMessage = '';
    this.source = this.editor.value;
    this.lineStarts = [0];
    for (const match of this.source.matchAll(/\n/g)) this.lineStarts.push(match.index + 1);
    this.lineError = '';
    this.search();
  }

  updateSelection() {
    if (this.mode === 'find') this.render();
  }

  locate(position: SourceSelection) {
    if (!Number.isSafeInteger(position.start) || !Number.isSafeInteger(position.end)
      || position.start < 0 || position.end < position.start || position.end > this.editor.value.length) return;
    this.editor.setSelectionRange(position.start, position.end);
    revealOffset(this.editor, position.start); this.onPosition();
  }

  close(): boolean {
    if (!this.mode) return false;
    this.mode = undefined; this.render();
    const { scrollTop, scrollLeft } = this.editor;
    this.editor.focus({ preventScroll: true });
    this.editor.scrollTop = scrollTop; this.editor.scrollLeft = scrollLeft;
    this.onPosition();
    return true;
  }

  private open(mode: 'find' | 'line') {
    this.mode = mode; this.lineError = '';
    if (mode === 'line') {
      const caret = this.editor.selectionDirection === 'backward' ? this.editor.selectionStart : this.editor.selectionEnd;
      this.line.value = String(this.source.slice(0, caret).split('\n').length);
    }
    this.render();
    const input = mode === 'find' ? this.query : this.line;
    input.focus({ preventScroll: true }); input.select();
  }

  private openReplace() {
    this.mode = 'find'; this.lineError = ''; this.replaceOpened = true; this.replaceMessage = '';
    this.render();
    this.replacement.focus({ preventScroll: true }); this.replacement.select();
  }

  private replace(all: boolean) {
    if (this.mode !== 'find' || !this.replaceOpened || this.composing) return;
    // Native input normally keeps this snapshot current; recheck before any edit.
    if (this.source !== this.editor.value) this.updateSource();
    if (!this.matches.length) return;
    this.replaceError = false;
    if (!all && this.selectedIndex() < 0) {
      this.nearest();
      this.replaceMessage = '已定位匹配，再次点击替换';
    } else {
      const editor = this.editor;
      const before = { value: editor.value, start: editor.selectionStart, end: editor.selectionEnd,
        direction: editor.selectionDirection, top: editor.scrollTop, left: editor.scrollLeft };
      const edit = sourceReplaceEdit(before.value, this.query.value, this.replacement.value, {
        caseSensitive: this.caseSensitive, maxBytes: this.sourceLimit(),
        ...(all ? {} : { selection: { start: before.start, end: before.end } }),
      });
      if (edit === 'too-large') {
        this.replaceMessage = '替换后源码超过允许大小，请减少替换内容'; this.replaceError = true;
      } else if (!edit) {
        if (!all) this.navigate(1);
        this.replaceMessage = '文本相同，未修改源码';
      } else {
        const expected = before.value.slice(0, edit.from) + edit.text + before.value.slice(edit.to);
        editor.focus({ preventScroll: true }); editor.setSelectionRange(edit.from, edit.to);
        // One native transaction preserves undo, including a complete replace-all operation.
        try { document.execCommand('insertText', false, edit.text); } catch {}
        if (editor.value !== expected) {
          this.onEdit();
          if (editor.value === before.value) {
            editor.setSelectionRange(before.start, before.end, before.direction);
            editor.scrollTop = before.top; editor.scrollLeft = before.left;
            this.replaceMessage = '未能替换，请直接编辑源码';
          } else this.replaceMessage = '未能完整替换，请撤销后重试';
          this.replaceError = true;
        } else {
          this.onEdit();
          const end = Math.min(edit.from + this.replacement.value.length, editor.value.length);
          editor.setSelectionRange(end, end);
          if (!all && this.matches.length) this.nearest();
          else { revealOffset(editor, edit.from); this.onPosition(); }
          this.replaceMessage = `已替换 ${edit.count.toLocaleString('zh-CN')} 处`;
        }
      }
    }
    this.render(); this.replacement.focus({ preventScroll: true });
  }

  private search() {
    const result = findSourceMatches(this.source, this.query.value, this.caseSensitive);
    this.matches = result.matches; this.truncated = result.truncated;
    this.render();
  }

  private selectedIndex() {
    return this.matches.findIndex(match => match.start === this.editor.selectionStart && match.end === this.editor.selectionEnd);
  }

  private nearest() {
    if (!this.matches.length) return;
    const index = this.matches.findIndex(match => match.start >= this.editor.selectionStart);
    this.select(index < 0 ? 0 : index);
  }

  private navigate(direction: -1 | 1) {
    if (!this.matches.length) return;
    const selected = this.selectedIndex();
    let index: number;
    if (selected >= 0) index = (selected + direction + this.matches.length) % this.matches.length;
    else if (direction === 1) {
      index = this.matches.findIndex(match => match.start >= this.editor.selectionEnd);
      if (index < 0) index = 0;
    } else {
      index = this.matches.findLastIndex(match => match.end <= this.editor.selectionStart);
      if (index < 0) index = this.matches.length - 1;
    }
    this.select(index);
  }

  private select(index: number) {
    const match = this.matches[index];
    this.editor.setSelectionRange(match.start, match.end);
    revealOffset(this.editor, match.start);
    this.onPosition(); this.render();
  }

  private jump() {
    const line = Number(this.line.value);
    if (!/^\d+$/.test(this.line.value) || !Number.isSafeInteger(line) || line < 1 || line > this.lineStarts.length) {
      this.lineError = `请输入 1 至 ${this.lineStarts.length} 之间的整数行号`;
      this.render(); this.line.focus({ preventScroll: true }); return;
    }
    const offset = this.lineStarts[line - 1];
    this.close();
    this.editor.setSelectionRange(offset, offset);
    revealOffset(this.editor, offset); this.onPosition();
  }

  private queueHighlight() {
    if (this.paintFrame) return;
    this.paintFrame = requestAnimationFrame(() => {
      this.paintFrame = 0;
      const overlay = this.control('editor-match-overlay');
      const match = this.matches[this.selectedIndex()];
      if (!this.dialog.open || this.mode !== 'find' || !match || document.activeElement === this.editor) {
        overlay.replaceChildren(); return;
      }
      // Native textarea selections disappear when the search input owns focus.
      // Only paint the current range; the textarea still owns all text and editing.
      const marks = measureRange(this.editor, match.start, match.end).map(rect => {
        const mark = document.createElement('span');
        mark.className = 'editor-match-mark';
        Object.assign(mark.style, { top: `${rect.top - this.editor.scrollTop}px`,
          left: `${rect.left - this.editor.scrollLeft}px`, width: `${rect.width}px`, height: `${rect.height}px` });
        return mark;
      });
      overlay.replaceChildren(...marks);
    });
  }

  private render() {
    this.control('editor-navigation').hidden = !this.mode;
    for (const mode of ['find', 'line'] as const) {
      this.control(`editor-${mode}-controls`).hidden = this.mode !== mode;
      this.control(`editor-${mode}-toggle`).setAttribute('aria-expanded', String(this.mode === mode));
    }
    const replacing = this.mode === 'find' && this.replaceOpened;
    this.control('editor-replace-controls').hidden = !replacing;
    const replaceToggle = this.control('editor-replace-toggle');
    replaceToggle.setAttribute('aria-expanded', String(replacing));
    replaceToggle.setAttribute('aria-label', replacing ? '隐藏源码替换' : '显示源码替换');
    for (const kind of ['one', 'all']) this.control<HTMLButtonElement>(`editor-replace-${kind}`).disabled = !replacing || this.composing || !this.matches.length;
    const replaceStatus = this.control('editor-replace-status');
    replaceStatus.hidden = !replacing || !this.replaceMessage;
    if (replaceStatus.textContent !== this.replaceMessage) replaceStatus.textContent = this.replaceMessage;
    replaceStatus.classList.toggle('error', this.replaceError);
    const selected = this.selectedIndex();
    const count = `${Math.max(0, selected + 1)}/${this.matches.length}${this.truncated ? '+' : ''}`;
    const position = this.control('editor-find-position');
    if (position.textContent !== count) position.textContent = count;
    this.control('editor-find-case').setAttribute('aria-pressed', String(this.caseSensitive));
    for (const direction of ['prev', 'next']) this.control<HTMLButtonElement>(`editor-find-${direction}`).disabled = !this.matches.length;
    this.line.max = String(this.lineStarts.length);
    this.line.setAttribute('aria-invalid', String(Boolean(this.lineError)));
    this.control('editor-line-range').textContent = `/ ${this.lineStarts.length} 行`;
    const error = this.control('editor-line-error');
    error.hidden = this.mode !== 'line' || !this.lineError;
    error.textContent = this.lineError;
    this.queueHighlight();
  }
}
