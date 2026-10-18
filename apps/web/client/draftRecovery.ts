import { decodeTaskDraft, encodeTaskDraft, type TaskDraft } from './draft';

export const draftRecoveryStorageKey = 'theorem-os.web-draft-recovery.v1';
export const replacementReasons = ['template', 'reset', 'reuse', 'import', 'source', 'edit'] as const;
export type ReplacementReason = typeof replacementReasons[number];
type Recovery = { draft: TaskDraft; reason: ReplacementReason; persisted: boolean };
type RecoveryStorage = Pick<Storage, 'getItem' | 'setItem' | 'removeItem'>;

// Keep one replacement, independent of autosave. Only editable fields are retained.
function copyDraft(draft: TaskDraft): TaskDraft {
  return { providerId: draft.providerId, model: draft.model, source: draft.source, task: draft.task,
    maxTurns: draft.maxTurns, maxRunSeconds: draft.maxRunSeconds, workers: draft.workers,
    effort: draft.effort, environment: draft.environment, coordination: draft.coordination, templateId: draft.templateId };
}

export class DraftRecovery {
  private value?: Recovery;

  constructor(private readonly storage: () => RecoveryStorage) {}

  get current(): Recovery | undefined {
    return this.value ? { ...this.value, draft: copyDraft(this.value.draft) } : undefined;
  }

  load() {
    this.value = undefined;
    try {
      const stored = this.storage().getItem(draftRecoveryStorageKey);
      if (!stored) return;
      const envelope: unknown = JSON.parse(stored);
      if (!envelope || typeof envelope !== 'object' || !Object.hasOwn(envelope, 'schema')
        || !Object.hasOwn(envelope, 'reason') || !Object.hasOwn(envelope, 'task')) throw new Error('Invalid recovery');
      const item = envelope as Record<string, unknown>;
      if (item.schema !== draftRecoveryStorageKey || !replacementReasons.includes(item.reason as ReplacementReason)) throw new Error('Invalid recovery');
      this.value = { draft: decodeTaskDraft(item.task), reason: item.reason as ReplacementReason, persisted: true };
    } catch { this.removeStored(); }
  }

  remember(before: TaskDraft, after: TaskDraft, reason: ReplacementReason) {
    const draft = copyDraft(before);
    if (JSON.stringify(draft) === JSON.stringify(copyDraft(after))) return;
    this.value = { draft, reason, persisted: false };
    try {
      const task: unknown = JSON.parse(encodeTaskDraft(draft));
      this.storage().setItem(draftRecoveryStorageKey, JSON.stringify({ schema: draftRecoveryStorageKey, reason, task }));
      this.value.persisted = true;
    } catch { this.removeStored(); }
  }

  clear() {
    this.value = undefined;
    this.removeStored();
  }

  private removeStored() {
    try { this.storage().removeItem(draftRecoveryStorageKey); } catch { /* In-memory recovery remains usable. */ }
  }
}
