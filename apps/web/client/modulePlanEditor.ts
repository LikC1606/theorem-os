import {
  defaultResearchModulePlan, researchModulePlanSchema,
  type CustomResearchModule, type ResearchModulePlan, type ResearchModuleSlot,
} from '../../../src/solver/modules/policy';

type ModuleField = 'enabled' | 'name' | 'slot' | 'mode' | 'instructions';
type ModuleControl = HTMLInputElement | HTMLSelectElement | HTMLTextAreaElement;
type ModuleRow = { element: HTMLElement; index: HTMLElement; controls: Record<ModuleField, ModuleControl>;
  disclosure: HTMLButtonElement; name: HTMLElement; meta: HTMLElement; body: HTMLElement;
  up: HTMLButtonElement; down: HTMLButtonElement; duplicate: HTMLButtonElement; remove: HTMLButtonElement; bytes: HTMLElement };
type PlanIssue = { path: (string | number)[]; message: string };

const maxModules = 8, maxRuleBytes = 4000, maxTotalBytes = 16000;
const encoder = new TextEncoder();
const byteSize = (value: string) => encoder.encode(value).length;
const clonePlan = (plan: ResearchModulePlan): ResearchModulePlan => ({ ...plan, custom: plan.custom.map(module => ({ ...module })) });
const customId = () => `custom-${typeof crypto.randomUUID === 'function' ? crypto.randomUUID().replaceAll('-', '').slice(0, 24)
  : Array.from(crypto.getRandomValues(new Uint32Array(3)), value => value.toString(16).padStart(8, '0')).join('')}`;
const slots: Array<[ResearchModuleSlot, string]> = [
  ['M1', 'M1 · 证明构造'], ['M3', 'M3 · 搜索决策'], ['M4', 'M4 · 上下文选择'], ['M5', 'M5 · 协作与复用'],
];

function create<T extends keyof HTMLElementTagNameMap>(tag: T, className?: string, content?: string) {
  const element = document.createElement(tag);
  if (className) element.className = className;
  if (content !== undefined) element.textContent = content;
  return element;
}

function selectOptions(options: ReadonlyArray<readonly [string, string]>) {
  const select = create('select');
  for (const [value, label] of options) {
    const option = create('option', undefined, label); option.value = value; select.append(option);
  }
  return select;
}

export class ModulePlanEditor {
  private plan = defaultResearchModulePlan();
  private rows = new Map<string, ModuleRow>();
  private deleted?: { module: CustomResearchModule; index: number; row: ModuleRow };
  private rowSequence = 0;
  private validationShown = false;
  private readonly scheduler: HTMLSelectElement;
  private readonly context: HTMLSelectElement;
  private readonly list: HTMLElement;
  private readonly add: HTMLButtonElement;
  private readonly expandAll: HTMLButtonElement;
  private readonly collapseAll: HTMLButtonElement;
  private readonly undoDelete: HTMLButtonElement;
  private readonly deletionNotice: HTMLElement;
  private readonly error: HTMLElement;

  constructor(private readonly root: HTMLElement, private readonly icons: (root: HTMLElement) => void,
    private readonly onChange: () => void) {
    this.scheduler = this.control('#module-plan-scheduler');
    this.context = this.control('#module-plan-context');
    this.list = this.control('[data-module-plan-list]');
    this.add = this.control('#module-plan-add');
    this.expandAll = this.control('[data-module-plan-expand-all]');
    this.collapseAll = this.control('[data-module-plan-collapse-all]');
    this.undoDelete = this.control('[data-module-plan-undo]');
    this.deletionNotice = this.control('[data-module-plan-deletion]');
    this.error = this.control('#module-plan-error');
    this.undoDelete.addEventListener('click', () => this.restoreDeleted());
    this.expandAll.addEventListener('click', () => { for (const row of this.rows.values()) this.setExpanded(row, true); });
    this.collapseAll.addEventListener('click', () => { for (const row of this.rows.values()) this.setExpanded(row, false); });
    this.scheduler.addEventListener('change', () => {
      this.plan.scheduler = this.scheduler.value as ResearchModulePlan['scheduler']; this.changed();
    });
    this.context.addEventListener('change', () => {
      this.plan.context = this.context.value as ResearchModulePlan['context']; this.changed();
    });
    this.list.addEventListener('input', event => {
      const target = event.target as ModuleControl, field = target.dataset.modulePlanField;
      if (field !== 'name' && field !== 'instructions') return;
      const module = this.moduleFor(target);
      if (!module) return;
      module[field] = target.value; this.changed();
    });
    this.list.addEventListener('change', event => {
      const target = event.target as ModuleControl, field = target.dataset.modulePlanField;
      const module = this.moduleFor(target);
      if (!module) return;
      if (field === 'enabled') module.enabled = (target as HTMLInputElement).checked;
      else if (field === 'slot') module.slot = target.value as ResearchModuleSlot;
      else if (field === 'mode') module.mode = target.value as CustomResearchModule['mode'];
      else return;
      this.changed();
    });
    this.list.addEventListener('click', event => {
      const target = event.target as Element;
      const button = target.closest<HTMLButtonElement>('[data-module-plan-disclosure],[data-module-plan-move],[data-module-plan-duplicate],[data-module-plan-delete]');
      if (!button || button.disabled) return;
      const module = this.moduleFor(button);
      if (!module) return;
      const index = this.plan.custom.indexOf(module), row = this.rows.get(module.id)!;
      if (button.hasAttribute('data-module-plan-disclosure')) {
        this.setExpanded(row, row.body.hidden); return;
      }
      const direction = button.dataset.modulePlanMove;
      if (direction) {
        const destination = index + (direction === 'up' ? -1 : 1);
        if (destination < 0 || destination >= this.plan.custom.length) return;
        this.plan.custom.splice(index, 1); this.plan.custom.splice(destination, 0, module);
        this.reconcile(); this.changed();
        const focus = button.disabled ? direction === 'up' ? row.down : row.up : button;
        focus.focus({ preventScroll: true }); row.element.scrollIntoView({ block: 'nearest', behavior: 'instant' });
        return;
      }
      if (button.hasAttribute('data-module-plan-duplicate')) {
        if (this.plan.custom.length >= maxModules) return;
        const sourceName = module.name.trim() || `自定义策略 ${index + 1}`;
        let name: string, number = 1;
        do {
          const suffix = number === 1 ? ' 副本' : ` 副本 ${number}`;
          let prefix = '';
          for (const character of sourceName) {
            if (prefix.length + character.length + suffix.length > 40) break;
            prefix += character;
          }
          name = `${prefix}${suffix}`; number++;
        } while (this.plan.custom.some(item => item.name === name));
        let id: string;
        do { id = customId(); } while (this.rows.has(id));
        const copy: CustomResearchModule = { ...module, id, name, enabled: false };
        this.plan.custom.splice(index + 1, 0, copy);
        this.reconcile(); this.changed();
        const nameControl = this.rows.get(id)!.controls.name as HTMLInputElement;
        nameControl.focus(); nameControl.select();
        return;
      }
      this.deleted = { module: { ...module }, index, row };
      this.plan.custom.splice(index, 1);
      this.reconcile(); this.changed();
      const next = this.plan.custom[Math.min(index, this.plan.custom.length - 1)];
      const nextRow = next ? this.rows.get(next.id)! : undefined;
      (nextRow ? nextRow.body.hidden ? nextRow.disclosure : nextRow.controls.name : this.add).focus();
    });
    this.add.addEventListener('click', () => this.addRule());
    this.setValue();
  }

  value(): ResearchModulePlan { return clonePlan(this.plan); }

  clearDeleted(): void {
    this.deleted = undefined;
    this.updateDeletionNotice();
  }

  setRuleEnabled(id: string, enabled: boolean): boolean {
    const module = this.plan.custom.find(module => module.id === id);
    if (!module || module.enabled === enabled) return false;
    module.enabled = enabled;
    (this.rows.get(id)!.controls.enabled as HTMLInputElement).checked = enabled;
    this.changed();
    return true;
  }

  addRule(slot: ResearchModuleSlot = 'M1'): string | undefined {
    if (this.plan.custom.length >= maxModules || !slots.some(([value]) => value === slot)) return;
    let number = this.plan.custom.length + 1;
    while (this.plan.custom.some(module => module.name === `自定义策略 ${number}`)) number++;
    let id: string;
    do { id = customId(); } while (this.rows.has(id));
    const module: CustomResearchModule = { id, name: `自定义策略 ${number}`, slot, mode: 'append', enabled: false, instructions: '' };
    this.plan.custom.push(module);
    this.reconcile(); this.changed();
    const name = this.rows.get(id)!.controls.name as HTMLInputElement;
    name.focus(); name.select();
    return id;
  }

  focusRule(id: string): void {
    const row = this.rows.get(id);
    if (!row) return;
    this.setExpanded(row, true);
    row.controls.instructions.focus({ preventScroll: true });
    row.controls.instructions.scrollIntoView({ block: 'nearest', behavior: 'instant' });
  }

  setValue(plan?: ResearchModulePlan): void {
    this.clearDeleted();
    this.plan = clonePlan(plan ?? defaultResearchModulePlan());
    if (this.scheduler.value !== this.plan.scheduler) this.scheduler.value = this.plan.scheduler;
    if (this.context.value !== this.plan.context) this.context.value = this.plan.context;
    this.reconcile(); this.updateCounts(); this.showError();
  }

  showError(message?: string): void {
    this.validationShown = Boolean(message);
    const result = message ? researchModulePlanSchema.safeParse(this.plan) : undefined;
    const issue = result && !result.success ? result.error.issues[0] : undefined;
    this.displayError(message, issue ? this.issueControl(issue) : undefined);
  }

  validate(): string | undefined {
    this.validationShown = true;
    return this.check(true);
  }

  private control<T extends HTMLElement>(selector: string): T {
    const element = this.root.querySelector<T>(selector);
    if (!element) throw new Error(`Missing module plan control: ${selector}`);
    return element;
  }

  private restoreDeleted(): void {
    const deleted = this.deleted;
    if (!deleted || this.plan.custom.length >= maxModules || this.plan.custom.some(module => module.id === deleted.module.id)) return;
    this.plan.custom.splice(Math.min(deleted.index, this.plan.custom.length), 0, deleted.module);
    this.rows.set(deleted.module.id, deleted.row);
    this.clearDeleted();
    this.reconcile(); this.changed();
    const focus = deleted.row.body.hidden ? deleted.row.disclosure : deleted.row.controls.name;
    focus.focus();
  }

  private updateDeletionNotice() {
    this.deletionNotice.hidden = !this.deleted;
    this.control('[data-module-plan-deleted-name]').textContent = this.deleted
      ? `已删除 ${this.deleted.module.name || '未命名策略'}` : '';
    this.undoDelete.disabled = !this.deleted || this.plan.custom.length >= maxModules;
    this.undoDelete.title = this.plan.custom.length >= maxModules
      ? '已达 8 项上限，无法恢复此策略' : `撤销删除${this.deleted?.module.name || '策略'}`;
    this.undoDelete.setAttribute('aria-label', this.undoDelete.title);
  }

  private moduleFor(target: Element) {
    const id = target.closest<HTMLElement>('[data-module-plan-id]')?.dataset.modulePlanId;
    return this.plan.custom.find(module => module.id === id);
  }

  private createRow(): ModuleRow {
    const prefix = `module-plan-rule-${++this.rowSequence}`;
    const element = create('article', 'module-plan-row');
    const heading = create('div', 'module-plan-row-heading');
    const toggle = create('label', 'module-plan-toggle');
    const enabled = create('input'); enabled.type = 'checkbox'; enabled.dataset.modulePlanField = 'enabled';
    toggle.append(enabled, create('span', undefined, '启用'));
    const index = create('span', 'module-plan-row-index');
    const disclosure = create('button', 'module-plan-disclosure');
    disclosure.type = 'button'; disclosure.dataset.modulePlanDisclosure = '';
    disclosure.setAttribute('aria-controls', `${prefix}-body`);
    const chevron = create('i'); chevron.dataset.lucide = 'chevron-down';
    const caption = create('span', 'module-plan-summary-copy');
    const summaryName = create('span', 'module-plan-summary-name'), meta = create('span', 'module-plan-summary-meta');
    caption.append(index, summaryName, meta); disclosure.append(chevron, caption);
    const actions = create('div', 'module-plan-row-actions');
    const up = create('button', 'icon-button module-plan-move');
    up.type = 'button'; up.dataset.modulePlanMove = 'up';
    const upIcon = create('i'); upIcon.dataset.lucide = 'arrow-up'; up.append(upIcon);
    const down = create('button', 'icon-button module-plan-move');
    down.type = 'button'; down.dataset.modulePlanMove = 'down';
    const downIcon = create('i'); downIcon.dataset.lucide = 'arrow-down'; down.append(downIcon);
    const duplicate = create('button', 'icon-button module-plan-duplicate');
    duplicate.type = 'button'; duplicate.dataset.modulePlanDuplicate = '';
    const copy = create('i'); copy.dataset.lucide = 'copy-plus'; duplicate.append(copy);
    const remove = create('button', 'icon-button module-plan-delete');
    remove.type = 'button'; remove.dataset.modulePlanDelete = '';
    const trash = create('i'); trash.dataset.lucide = 'trash-2'; remove.append(trash);
    actions.append(up, down, duplicate, remove); heading.append(disclosure, toggle, actions);

    const fields = create('div', 'module-plan-fields');
    const name = create('input'); name.type = 'text'; name.maxLength = 40; name.autocomplete = 'off'; name.spellcheck = false;
    const slot = selectOptions(slots);
    const mode = selectOptions([['append', '补充默认建议'], ['replace', '替换默认建议']]);
    const instructions = create('textarea'); instructions.rows = 3; instructions.spellcheck = false;
    const controls = { enabled, name, slot, mode, instructions };
    for (const [field, label] of [['name', '名称'], ['slot', '所属模块'], ['mode', '策略方式']] as const) {
      const wrapper = create('div', `module-plan-${field}-field`), control = controls[field];
      control.id = `${prefix}-${field}`; control.dataset.modulePlanField = field;
      control.setAttribute('aria-describedby', 'module-plan-error');
      const caption = create('label', undefined, label); caption.htmlFor = control.id;
      wrapper.append(caption, control); fields.append(wrapper);
    }
    const rule = create('div', 'module-plan-instructions-field');
    instructions.id = `${prefix}-instructions`; instructions.dataset.modulePlanField = 'instructions';
    instructions.setAttribute('aria-describedby', `${prefix}-bytes module-plan-error`);
    const ruleHeading = create('div', 'module-plan-rule-heading');
    const label = create('label', undefined, '规则'); label.htmlFor = instructions.id;
    const bytes = create('span', 'module-plan-rule-bytes mono'); bytes.id = `${prefix}-bytes`; bytes.dataset.modulePlanRuleBytes = '';
    ruleHeading.append(label, bytes); rule.append(ruleHeading, instructions);
    const body = create('div', 'module-plan-row-body'); body.id = `${prefix}-body`;
    body.append(fields, rule); element.append(heading, body);
    this.icons(element);
    return { element, index, controls, disclosure, name: summaryName, meta, body, up, down, duplicate, remove, bytes };
  }

  private reconcile() {
    const ids = new Set(this.plan.custom.map(module => module.id));
    for (const [id, row] of this.rows) if (!ids.has(id)) { row.element.remove(); this.rows.delete(id); }
    let cursor = this.list.firstElementChild;
    for (const [index, module] of this.plan.custom.entries()) {
      let row = this.rows.get(module.id);
      if (!row) { row = this.createRow(); this.rows.set(module.id, row); row.element.dataset.modulePlanId = module.id; }
      row.index.textContent = `策略 ${index + 1}`;
      row.element.setAttribute('aria-label', `自定义策略 ${index + 1}`);
      const enabled = row.controls.enabled as HTMLInputElement;
      if (enabled.checked !== module.enabled) enabled.checked = module.enabled;
      for (const field of ['name', 'slot', 'mode', 'instructions'] as const)
        if (row.controls[field].value !== module[field]) row.controls[field].value = module[field];
      if (row.element !== cursor) this.list.insertBefore(row.element, cursor);
      cursor = row.element.nextElementSibling;
    }
  }

  private updateCounts() {
    let total = 0;
    for (const [index, module] of this.plan.custom.entries()) {
      const row = this.rows.get(module.id)!, count = byteSize(module.instructions);
      total += count; row.element.dataset.enabled = String(module.enabled);
      row.bytes.textContent = `${count} / ${maxRuleBytes} B`;
      row.bytes.dataset.overLimit = String(count > maxRuleBytes);
      const name = module.name || `策略 ${index + 1}`;
      row.name.textContent = name;
      row.meta.textContent = `${slots.find(([slot]) => slot === module.slot)?.[1] ?? module.slot} · ${module.mode === 'replace' ? '替换建议' : '补充建议'}`;
      this.setExpanded(row, !row.body.hidden);
      row.controls.enabled.setAttribute('aria-label', `启用${name}`);
      row.up.disabled = index === 0; row.down.disabled = index === this.plan.custom.length - 1;
      row.up.title = row.up.disabled ? '已是第一项策略' : `上移${name}`;
      row.down.title = row.down.disabled ? '已是最后一项策略' : `下移${name}`;
      row.up.setAttribute('aria-label', row.up.title); row.down.setAttribute('aria-label', row.down.title);
      row.remove.title = `删除${module.name || `策略 ${index + 1}`}`;
      row.remove.setAttribute('aria-label', row.remove.title);
      row.duplicate.disabled = this.plan.custom.length >= maxModules;
      row.duplicate.title = row.duplicate.disabled ? '最多保存 8 个自定义策略，删除后可继续复制'
        : `复制${module.name || `策略 ${index + 1}`}（副本默认停用）`;
      row.duplicate.setAttribute('aria-label', row.duplicate.title);
    }
    this.control('[data-module-plan-count]').textContent = `${this.plan.custom.length} / ${maxModules}`;
    const bytes = this.control('[data-module-plan-bytes]');
    bytes.textContent = `${total} / ${maxTotalBytes} B`; bytes.dataset.overLimit = String(total > maxTotalBytes);
    this.add.disabled = this.plan.custom.length >= maxModules;
    this.add.title = this.add.disabled ? '最多添加 8 个自定义策略' : '新增自定义策略';
    this.expandAll.disabled = !this.plan.custom.length; this.collapseAll.disabled = !this.plan.custom.length;
    this.updateDeletionNotice();
  }

  private setExpanded(row: ModuleRow, expanded: boolean) {
    row.body.hidden = !expanded; row.element.dataset.expanded = String(expanded);
    row.disclosure.setAttribute('aria-expanded', String(expanded));
    row.disclosure.title = `${expanded ? '收起' : '展开'}${row.name.textContent}`;
    row.disclosure.setAttribute('aria-label', `${row.disclosure.title} · ${row.meta.textContent}`);
  }

  private changed() {
    this.updateCounts();
    if (this.validationShown) this.check(false);
    else this.displayError();
    this.onChange();
  }

  private check(focus: boolean): string | undefined {
    const result = researchModulePlanSchema.safeParse(this.plan);
    const issue = result.success ? undefined : result.error.issues[0];
    const message = issue ? this.issueMessage(issue) : undefined;
    const control = issue ? this.issueControl(issue) : undefined;
    this.displayError(message, control);
    if (focus && message) {
      const module = control && this.moduleFor(control), row = module && this.rows.get(module.id);
      if (row) this.setExpanded(row, true);
      (control ?? this.root).focus();
    }
    return message;
  }

  private issueControl(issue: PlanIssue): ModuleControl | HTMLButtonElement | undefined {
    if (issue.path[0] === 'scheduler') return this.scheduler;
    if (issue.path[0] === 'context') return this.context;
    if (issue.path[0] !== 'custom') return;
    const index = typeof issue.path[1] === 'number' ? issue.path[1] : undefined;
    const module = index === undefined ? undefined : this.plan.custom[index];
    const row = module ? this.rows.get(module.id) : undefined;
    const field = issue.path[2];
    if (row && field === 'id') return row.remove;
    if (row && ['enabled', 'name', 'slot', 'mode', 'instructions'].includes(String(field))) return row.controls[field as ModuleField];
    if (row) return row.controls.instructions;
    return this.plan.custom.map(module => this.rows.get(module.id)!.controls.instructions)
      .find(control => byteSize(control.value) > maxRuleBytes);
  }

  private issueMessage(issue: PlanIssue): string {
    if (issue.path[0] === 'scheduler') return '请选择有效的搜索策略。';
    if (issue.path[0] === 'context') return '请选择有效的上下文策略。';
    const index = typeof issue.path[1] === 'number' ? issue.path[1] : undefined;
    const module = index === undefined ? undefined : this.plan.custom[index];
    const prefix = index === undefined ? '' : `策略 ${index + 1}：`;
    if (module && issue.path[2] === 'name') return `${prefix}${module.name.includes('\0') ? '名称不能包含空字符。'
      : module.name.trim() ? '名称最多 40 个字符。' : '请填写名称。'}`;
    if (module && issue.path[2] === 'instructions') return `${prefix}${module.instructions.includes('\0') ? '规则不能包含空字符。'
      : module.instructions.trim() ? '规则最多 4000 字节。' : '启用前请填写规则。'}`;
    if (module && issue.path[2] === 'slot') return `${prefix}请选择 M1、M3、M4 或 M5。`;
    if (module && issue.path[2] === 'id') return `${prefix}策略 ID 无效，请删除此项后重新添加。`;
    if (module && issue.path[2] === 'mode') return module.enabled && module.mode === 'replace'
      ? `${module.slot} 只能启用一个「替换默认建议」策略。` : `${prefix}请选择有效的策略方式。`;
    if (this.plan.custom.length > maxModules) return '最多添加 8 个自定义策略。';
    if (this.plan.custom.reduce((total, module) => total + byteSize(module.instructions), 0) > maxTotalBytes)
      return '全部规则合计最多 16000 字节。';
    return `${prefix}${issue.message || '请检查模块方案。'}`;
  }

  private displayError(message?: string, control?: ModuleControl | HTMLButtonElement) {
    for (const invalid of this.root.querySelectorAll('[aria-invalid="true"]')) invalid.removeAttribute('aria-invalid');
    for (const row of this.rows.values()) row.element.dataset.invalid = 'false';
    if (message && control) control.setAttribute('aria-invalid', 'true');
    if (message && control) {
      const module = this.moduleFor(control);
      if (module) this.rows.get(module.id)!.element.dataset.invalid = 'true';
    }
    this.error.textContent = message ?? ''; this.error.hidden = !message;
  }
}
