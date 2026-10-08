/**
 * Session-local Team agent identifiers.
 *
 * Core keeps the persisted slot_id as the authoritative backend identity. MCP
 * callers can use the shorter A001-style alias, which is resolved at the
 * local tool boundary before permission checks or Core requests are made.
 */

export type TeamAgentIdMember = Readonly<{ slotId: string }>;

const TEAM_AGENT_ALIAS_PATTERN = /^A(\d{3})$/u;

export function createTeamAgentId(index: number): string {
  if (!Number.isInteger(index) || index < 0 || index > 999) {
    throw new TypeError('Team member index is invalid');
  }
  return `A${String(index + 1).padStart(3, '0')}`;
}

export function resolveTeamAgentSlotId(
  value: unknown,
  members: readonly TeamAgentIdMember[],
  field = 'target_slot_id'
): string {
  const normalized = String(value ?? '').trim();
  if (!normalized) throw new Error(`${field} is required`);

  // Preserve backwards compatibility with persisted/Core-authenticated IDs.
  const exact = members.find((member) => member.slotId === normalized);
  if (exact) return exact.slotId;

  const match = TEAM_AGENT_ALIAS_PATTERN.exec(normalized);
  if (!match) throw new Error(`${field} does not match a Team agent id or slot_id`);
  const member = members[Number(match[1]) - 1];
  if (!member?.slotId) throw new Error(`${field} points outside this Team roster`);
  return member.slotId;
}

export function teamAgentIdForSlotId(slotId: string, members: readonly TeamAgentIdMember[]): string | undefined {
  const index = members.findIndex((member) => member.slotId === slotId);
  return index >= 0 ? createTeamAgentId(index) : undefined;
}
