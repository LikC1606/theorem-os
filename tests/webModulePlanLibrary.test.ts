import { describe, expect, it } from 'vitest';
import { ModulePlanLibrary, modulePlanLibraryLimit, modulePlanLibraryStorageKey } from '../apps/web/client/modulePlanLibrary';
import { defaultResearchModulePlan, type ResearchModulePlan } from '../src/solver/modules/policy';

function setup() {
  const values = new Map<string, string>();
  const storage = { getItem: (key: string) => values.get(key) ?? null, setItem: (key: string, value: string) => { values.set(key, value); } };
  let pending: Promise<unknown> = Promise.resolve();
  const lock = <T>(change: () => T): Promise<T> => {
    const result = pending.then(change); pending = result.catch(() => {}); return result;
  };
  return { values, storage, lock, library: new ModulePlanLibrary(() => storage, lock), other: new ModulePlanLibrary(() => storage, lock) };
}
const plan = (): ResearchModulePlan => ({ scheduler: 'critical-path', context: 'essential', custom: [
  { id: 'draft-policy', slot: 'M1', mode: 'replace', enabled: true, name: '', instructions: '' },
] });

describe('browser-local module plan library', () => {
  it('retains unfinished configurations independently of later edits and reads', async () => {
    const { library, other } = setup(), source = plan();
    const saving = library.save('  Proof workflow  ', source);
    source.custom[0].instructions = 'A later edit';
    const saved = await saving;
    saved.plan.custom[0].name = 'A changed return value';
    expect(other.list()).toEqual([{ ...saved, plan: plan() }]);
    const read = library.list(); read[0].plan.custom[0].enabled = false;
    expect(library.list()[0].plan).toEqual(plan());
    expect(library.list()[0].name).toBe('Proof workflow');
  });

  it('reads current storage for updates, removes and restores without losing other tabs\' plans', async () => {
    const { library, other } = setup();
    const first = await library.save('First', plan());
    const second = await other.save('Second', defaultResearchModulePlan());
    const updated = await library.save('Renamed', { ...plan(), context: 'full' }, first);
    expect(other.list().map(entry => entry.name)).toEqual(['Renamed', 'Second']);
    await other.remove(second);
    const third = await library.save('Third', defaultResearchModulePlan());
    await other.restore(second);
    expect(library.list()).toEqual([second, third, updated]);
    await other.restore(second);
    expect(library.list()).toHaveLength(3);
  });

  it('refuses to overwrite or remove a concurrently changed or deleted selection', async () => {
    const { library, other } = setup();
    const first = await library.save('Original', plan());
    const updated = await other.save('Updated elsewhere', defaultResearchModulePlan(), first);
    await expect(library.save('Old tab edit', plan(), first)).rejects.toThrow('其他页面修改或删除');
    await expect(library.remove(first)).rejects.toThrow('其他页面修改或删除');
    expect(library.list()).toEqual([updated]);
    await other.remove(updated);
    await expect(library.save('Old tab edit', plan(), updated)).rejects.toThrow('其他页面修改或删除');
    expect(library.list()).toEqual([]);
  });

  it('limits new entries while allowing updates and reports capacity conflicts during restore', async () => {
    const { library, other } = setup();
    const entries = await Promise.all(Array.from({ length: modulePlanLibraryLimit }, (_, index) => library.save(`Plan ${index}`, plan())));
    await expect(other.save('Too many', plan())).rejects.toThrow('12 项上限');
    const updated = await other.save('Updated at capacity', defaultResearchModulePlan(), entries[0]);
    await library.remove(updated); await other.save('Another tab filled the slot', plan());
    await expect(library.restore(updated)).rejects.toThrow('12 项上限');
    expect(library.list()).toHaveLength(modulePlanLibraryLimit);
  });

  it('requires distinct trimmed names and preserves both snapshots on a restore name conflict', async () => {
    const { library, other } = setup();
    const first = await library.save('Workflow', plan());
    await expect(other.save(' workflow ', plan())).rejects.toThrow('同名方案');
    await expect(library.save('  ', plan())).rejects.toThrow('方案名称');
    await expect(library.save('x'.repeat(41), plan())).rejects.toThrow('方案名称');
    await library.remove(first);
    const replacement = await other.save('Workflow', defaultResearchModulePlan());
    await expect(library.restore(first)).rejects.toThrow('同名方案');
    expect(library.list()).toEqual([replacement]);
  });

  it('keeps successful writes readable when JSON escaping expands otherwise valid rules', async () => {
    const { library, values } = setup();
    const expanded: ResearchModulePlan = { ...plan(), custom: Array.from({ length: 4 }, (_, index) => ({
      ...plan().custom[0], id: `escaped-${index}`, instructions: '\u0001'.repeat(4000),
    })) };
    let saved = 0;
    for (let index = 0; index < modulePlanLibraryLimit; index++) {
      const before = values.get(modulePlanLibraryStorageKey);
      try { await library.save(`Escaped ${index}`, expanded); saved++; }
      catch (error) {
        expect(error).toBeInstanceOf(Error);
        expect((error as Error).message).toContain('大小限制');
        expect(values.get(modulePlanLibraryStorageKey)).toBe(before);
      }
      expect(library.list()).toHaveLength(saved);
    }
    expect(saved).toBeGreaterThan(0);
  });

  it.each([
    'not-json', 'null', JSON.stringify({ schema: 'future-version', plans: [] }),
    JSON.stringify({ schema: modulePlanLibraryStorageKey, plans: [], apiKey: 'untrusted-extra' }),
    'x'.repeat(1024 * 1024 + 1),
  ])('keeps unreadable stored data intact rather than replacing it with an empty library (%#)', async stored => {
    const { library, values } = setup(); values.set(modulePlanLibraryStorageKey, stored);
    expect(() => library.list()).toThrow('格式无效');
    await expect(library.save('New', plan())).rejects.toThrow('格式无效');
    expect(values.get(modulePlanLibraryStorageKey)).toBe(stored);
  });

  it('reopens a preset saved with a removed scheduler under the default scheduler', async () => {
    const { library, values } = setup();
    const saved = await library.save('Retired', plan());
    values.set(modulePlanLibraryStorageKey, JSON.stringify({ schema: modulePlanLibraryStorageKey,
      plans: [{ ...saved, plan: { ...saved.plan, scheduler: 'primary-led' } }] }));
    expect(library.list()).toEqual([{ ...saved, plan: { ...plan(), scheduler: 'plan' } }]);
    await library.remove(library.list()[0]!);
    expect(library.list()).toEqual([]);
  });

  it('rejects duplicate identities, missing plan fields and executable or credential metadata', async () => {
    const { library, values } = setup();
    const saved = await library.save('Workflow', plan());
    for (const plans of [[saved, { ...saved, name: 'Another' }], [saved, { ...saved, id: 'saved-distinct_id_000', name: 'workflow' }],
      [{ ...saved, plan: { custom: [] } }], [{ ...saved, plan: { ...plan(), apiKey: 'not-allowed' } }],
      [{ ...saved, plan: { ...plan(), custom: [{ ...plan().custom[0], script: '/plugin.ts' }] } }]]) {
      const stored = JSON.stringify({ schema: modulePlanLibraryStorageKey, plans }); values.set(modulePlanLibraryStorageKey, stored);
      expect(() => library.list()).toThrow('格式无效');
      expect(values.get(modulePlanLibraryStorageKey)).toBe(stored);
    }
  });

  it('rejects fields outside the module schema before saving and never serializes the wider task', async () => {
    const { library, values } = setup();
    await expect(library.save('Unsafe', { ...plan(), apiKey: 'fixture-secret' } as ResearchModulePlan)).rejects.toThrow('草稿限制');
    const saved = await library.save('Only modules', plan());
    expect(JSON.parse(values.get(modulePlanLibraryStorageKey)!)).toEqual({ schema: modulePlanLibraryStorageKey, plans: [saved] });
    expect(values.size).toBe(1);
  });

  it('does not commit a save, delete or restore when storage access fails', async () => {
    const { library, storage, values, lock } = setup();
    const saved = await library.save('Original', plan());
    let before = values.get(modulePlanLibraryStorageKey);
    const blockedWrite = new ModulePlanLibrary(() => ({ ...storage, setItem: () => { throw new Error('quota'); } }), lock);
    await expect(blockedWrite.save('New', plan())).rejects.toThrow('写入失败');
    await expect(blockedWrite.save('Rename', plan(), saved)).rejects.toThrow('写入失败');
    await expect(blockedWrite.remove(saved)).rejects.toThrow('写入失败');
    expect(values.get(modulePlanLibraryStorageKey)).toBe(before);
    await library.remove(saved); before = values.get(modulePlanLibraryStorageKey);
    await expect(blockedWrite.restore(saved)).rejects.toThrow('写入失败');
    expect(values.get(modulePlanLibraryStorageKey)).toBe(before);
    const blockedRead = new ModulePlanLibrary(() => ({ ...storage, getItem: () => { throw new Error('denied'); } }), lock);
    await expect(blockedRead.save('New', plan())).rejects.toThrow('无法读取');
    expect(values.get(modulePlanLibraryStorageKey)).toBe(before);
  });
});
