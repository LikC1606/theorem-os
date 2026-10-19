export type ModelRequestUsage = {
  inputTokens: number;
  outputTokens: number;
  totalTokens: number;
  cachedInputTokens?: number;
  reasoningOutputTokens?: number;
};

export type ModelRequestReceipt = { usage?: ModelRequestUsage; complete: boolean };
export type ModelRequestAdmission =
  | { allowed: true; settle: (receipt: ModelRequestReceipt) => void }
  | { allowed: false; reason: 'math_total_token_limit' | 'math_model_usage_unavailable' | 'math_model_request_stopped' };

/** Admission and settlement are synchronous so another request cannot observe stale receipts. */
export type ModelRequestGate = () => ModelRequestAdmission;
