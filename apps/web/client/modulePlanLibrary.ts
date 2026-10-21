import { z } from 'zod';
import { researchModulePlanDraftSchema, type ResearchModulePlan } from '../../../src/solver/modules/policy';

export const modulePlanLibraryStorageKey = 'theorem-os.web-module-library.v1';
export const modulePlanLibraryLimit = 12;
export type SavedModulePlan = { id: string; name: string; plan: ResearchModulePlan; updatedAt: string };
type LibraryStorage = Pick<Storage, 'getItem' | 'setItem'>;
type LibraryLock = <T>(change: () => T) => Promise<T>;
const maximumLibraryCharacters = 1024 * 1024;

const nameSchema = z.string().trim().min(1).max(40).refine(value => !value.includes('\0'));
// Saved presets outlive removed strategies; such a preset reopens with the default scheduler instead of hiding the library.
const retiredSchedulers = new Set(['primary-led', 'goals-first']);
const savedPlanSchema = z.object({
  id: z.string().regex(/^saved-[A-Za-z0-9_-]{12,64}$/), name: nameSchema,
  plan: z.preprocess(plan => plan && typeof plan === 'object' && retiredSchedulers.has((plan as { scheduler?: unknown }).scheduler as string)
    ? { ...plan, scheduler: 'plan' } : plan, researchModulePlanDraftSchema), updatedAt: z.string().datetime(),
}).strict();
const librarySchema = z.object({
  schema: z.literal(modulePlanLibraryStorageKey), plans: z.array(savedPlanSchema).max(modulePlanLibraryLimit),
}).strict().superRefine(({ plans }, context) => {
  if (new Set(plans.map(plan => plan.id)).size !== plans.length
    || new Set(plans.map(plan => plan.name.toLowerCase())).size !== plans.length)
    context.addIssue({ code: z.ZodIssueCode.custom, message: 'Duplicate saved module plan' });
});
const newId = () => `saved-${typeof crypto.randomUUID === 'function' ? crypto.randomUUID()
  : Array.from(crypto.getRandomValues(new Uint32Array(4)), value => value.toString(16).padStart(8, '0')).join('')}`;
const equal = (left: SavedModulePlan, right: SavedModulePlan) => JSON.stringify(left) === JSON.stringify(right);
const lockLibrary: LibraryLock = async change => {
  if (typeof navigator === 'undefined' || !navigator.locks)
    throw new Error('当前页面无法安全写入方案库，请使用支持 Web Locks 的浏览器，通过 HTTPS 或 localhost 打开。');
  return navigator.locks.request(modulePlanLibraryStorageKey, change);
};

export class ModulePlanLibrary {
  constructor(private readonly storage: () => LibraryStorage, private readonly lock: LibraryLock = lockLibrary) {}

  list(): SavedModulePlan[] {
    let stored: string | null;
    try { stored = this.storage().getItem(modulePlanLibraryStorageKey); }
    catch { throw new Error('无法读取此浏览器的方案库，请检查本地存储设置。'); }
    if (stored === null) return [];
    try {
      if (stored.length > maximumLibraryCharacters) throw new Error('Oversized library');
      return librarySchema.parse(JSON.parse(stored)).plans as SavedModulePlan[];
    } catch { throw new Error('本地方案库格式无效，已保留原始数据。'); }
  }

  async save(name: string, plan: ResearchModulePlan, previous?: SavedModulePlan): Promise<SavedModulePlan> {
    const parsedName = nameSchema.safeParse(name);
    if (!parsedName.success) throw new Error('请填写 1 至 40 个字符的方案名称，且不含空字符。');
    const parsedPlan = researchModulePlanDraftSchema.safeParse(plan);
    if (!parsedPlan.success) throw new Error('模块方案超出草稿限制，暂时无法保存。');
    // Hold one origin-wide lock across read, validation and write to retain concurrent saves.
    return this.lock(() => {
      const plans = this.list();
      if (previous) this.checkCurrent(plans, previous);
      if (!previous && plans.length >= modulePlanLibraryLimit) throw new Error('方案库已达 12 项上限，请先删除不需要的方案。');
      this.checkName(plans, parsedName.data, previous?.id);
      const saved: SavedModulePlan = { id: previous?.id ?? newId(), name: parsedName.data,
        plan: parsedPlan.data as ResearchModulePlan, updatedAt: new Date().toISOString() };
      this.write([saved, ...plans.filter(plan => plan.id !== saved.id)]);
      return saved;
    });
  }

  async remove(previous: SavedModulePlan): Promise<void> {
    return this.lock(() => {
      const plans = this.list();
      this.checkCurrent(plans, previous);
      this.write(plans.filter(plan => plan.id !== previous.id));
    });
  }

  async restore(deleted: SavedModulePlan): Promise<SavedModulePlan> {
    const saved = savedPlanSchema.parse(deleted) as SavedModulePlan;
    return this.lock(() => {
      const plans = this.list(), existing = plans.find(plan => plan.id === saved.id);
      if (existing && equal(existing, saved)) return existing;
      if (existing) throw new Error('此方案已被其他页面修改，无法覆盖恢复。');
      if (plans.length >= modulePlanLibraryLimit) throw new Error('方案库已达 12 项上限，暂时无法恢复。');
      this.checkName(plans, saved.name);
      this.write([saved, ...plans]);
      return saved;
    });
  }

  private checkCurrent(plans: SavedModulePlan[], previous: SavedModulePlan) {
    const current = plans.find(plan => plan.id === previous.id);
    if (!current || !equal(current, previous)) throw new Error('此方案已被其他页面修改或删除，请重新选择后操作。');
  }

  private checkName(plans: SavedModulePlan[], name: string, id?: string) {
    if (plans.some(plan => plan.id !== id && plan.name.toLowerCase() === name.toLowerCase()))
      throw new Error('已有同名方案，请更换名称。');
  }

  private write(plans: SavedModulePlan[]) {
    const content = JSON.stringify({ schema: modulePlanLibraryStorageKey, plans });
    if (content.length > maximumLibraryCharacters) throw new Error('方案库内容超过本地大小限制，请先精简规则或删除不需要的方案。');
    try { this.storage().setItem(modulePlanLibraryStorageKey, content); }
    catch { throw new Error('方案库写入失败，请检查浏览器存储权限或剩余空间；本次操作未保存。'); }
  }
}
