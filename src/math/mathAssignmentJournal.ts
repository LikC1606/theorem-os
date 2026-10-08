import path from 'node:path';
import { z } from 'zod';
import type { RuntimeMathAssignment } from "../common/types/team/mathRuntimeContracts";
import { mathAssignmentShape, isMathRelativePath, normalizeMathAssignment } from "./mathPublicWire";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

const id = z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u);
const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const schema = z
  .object({
    schema: z.literal('deepscientist.math.assignment.v2'),
    runId: id,
    bindingDigest: digest,
    assignmentId: id,
    scopeId: id,
    baseCommit: z.string().regex(/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u),
    request: z.object(mathAssignmentShape).strict(),
    payloadHash: digest,
    sourceRootRelative: z.string().refine(isMathRelativePath),
    draftRoot: z.string().refine(path.isAbsolute),
    artifactGrants: z.array(id),
  })
  .strict();

export function normalizeRuntimeMathAssignment(value: unknown): RuntimeMathAssignment {
  const parsed = schema.safeParse(value);
  if (!parsed.success) throw new Error('math_assignment_wal_integrity');
  const assignment = parsed.data as RuntimeMathAssignment;
  const request = normalizeMathAssignment(assignment.request);
  if (
    mathDigest(canonicalMathJson(request)) !== assignment.payloadHash ||
    new Set(assignment.artifactGrants).size !== assignment.artifactGrants.length
  )
    throw new Error('math_assignment_wal_integrity');
  return Object.freeze({ ...assignment, request, artifactGrants: Object.freeze(assignment.artifactGrants) });
}

export function isRuntimeMathAssignment(value: unknown): value is RuntimeMathAssignment {
  try {
    normalizeRuntimeMathAssignment(value);
    return true;
  } catch {
    return false;
  }
}

export function decodeMathAssignmentJournal(value: unknown): Readonly<{
  version: 1 | 2;
  teamId: string;
  slotId: string;
  assignmentId: string;
  state: 'prepared' | 'accepted' | 'integrated' | 'superseded';
  assignment: unknown;
}> {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_assignment_wal_integrity');
  const record = value as Record<string, unknown>;
  if (
    !['deepscientist.research_team_assignment.v1', 'deepscientist.research_team_assignment.v2'].includes(
      String(record.schema)
    )
  )
    throw new Error('math_assignment_wal_schema_unsupported');
  if (
    !['teamId', 'slotId', 'assignmentId'].every((key) => typeof record[key] === 'string' && record[key].length > 0) ||
    !['prepared', 'accepted', 'integrated', 'superseded'].includes(String(record.state)) ||
    record.assignment === undefined
  )
    throw new Error('math_assignment_wal_integrity');
  const version = record.schema === 'deepscientist.research_team_assignment.v2' ? 2 : 1;
  if (version === 2) {
    const assignment = normalizeRuntimeMathAssignment(record.assignment);
    if (assignment.assignmentId !== record.assignmentId || assignment.request.targetSlotId !== record.slotId)
      throw new Error('math_assignment_wal_integrity');
  }
  // This mapping does not rewrite v1 identity, scope or persisted fields.
  return {
    version,
    teamId: record.teamId as string,
    slotId: record.slotId as string,
    assignmentId: record.assignmentId as string,
    state: record.state as 'prepared' | 'accepted' | 'integrated' | 'superseded',
    assignment: record.assignment,
  };
}
