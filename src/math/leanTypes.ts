/**
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const MATHEMATICS_VERIFICATION_EVENT_SCHEMA = 'deepscientist.mathematics.verification_event.v1' as const;
export type MathematicsVerificationStatus = 'pending' | 'kernel_verified' | 'failed' | 'blocked' | 'unavailable';

export type MathematicsGoalState = {
  stateId: string;
  target: string;
  hypotheses: string[];
  theoremName?: string;
};

export type MathematicsVerificationEventPayloadMap = {
  'session.opened': {
    projectRoot: string;
    itemCount: number;
    uniqueFileCount: number;
  };
  'toolchain.resolved': {
    command: 'lake' | 'lean';
    executable: string;
    lakeFile?: string;
    available?: boolean;
  };
  'formula.submitted': {
    formulaId: string;
    formula: string;
    label?: string;
    theoremName?: string;
    sourcePath?: string;
    authority: 'agent';
  };
  'goal.opened': MathematicsGoalState & {
    authority: 'agent' | 'lean-process';
  };
  'goal.rewritten': MathematicsGoalState & {
    parentStateId: string;
    previousTarget: string;
    authority: 'agent' | 'lean-process';
  };
  'goal.branched': MathematicsGoalState & {
    parentStateId: string;
    branchLabel?: string;
    authority: 'agent' | 'lean-process';
  };
  'goal.closed': {
    stateId: string;
    parentStateId?: string;
    target?: string;
    theoremName?: string;
  } & ({ status: 'draft_closed'; authority: 'agent' } | { status: 'kernel_verified'; authority: 'lean-kernel' });
  'file.opened': {
    proofPath: string;
    proofHash: string;
    bytes: number;
    checkCount: number;
  };
  'check.draft_checked': {
    proofPath: string;
    status: 'accepted' | 'rejected';
    sorryCount: number;
    admitCount: number;
    axioms: string[];
  };
  'diagnostic.emitted': {
    source: 'git' | 'safety' | 'process' | 'stdout' | 'stderr' | 'agent';
    severity: 'info' | 'warning' | 'error';
    message: string;
    proofPath?: string;
    stateId?: string;
  };
  'check.kernel_checked': {
    proofPath: string;
    status: MathematicsVerificationStatus;
    exitCode: number | null;
    signal: string | null;
    timedOut: boolean;
    aborted: boolean;
    durationMs: number;
  };
  'receipt.published': {
    receiptId: string;
    checkId: string;
    proofPath: string;
    theoremName?: string;
    status: MathematicsVerificationStatus;
  };
  'session.closed': {
    status: MathematicsVerificationStatus;
    resultCount: number;
    durationMs: number;
  };
};

export type MathematicsVerificationEventKind = keyof MathematicsVerificationEventPayloadMap;

export type MathematicsVerificationEvent = {
  [Kind in MathematicsVerificationEventKind]: {
    schema: typeof MATHEMATICS_VERIFICATION_EVENT_SCHEMA;
    eventId: string;
    sessionId: string;
    timestamp: number;
    kind: Kind;
    payload: MathematicsVerificationEventPayloadMap[Kind];
  };
}[MathematicsVerificationEventKind];
