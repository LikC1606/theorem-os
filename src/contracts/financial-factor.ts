/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/**
 * Pure financial-factor mode contract.
 *
 * This file intentionally has no Electron, Node, renderer, or configuration
 * imports. It is the one source for the policy block and the conversation
 * metadata shared by the desktop UI and the headless Developer Executor.
 */
export const FINANCIAL_FACTOR_RUNTIME_MODE_ID = 'financial_factor' as const;
export const FINANCIAL_FACTOR_DISCOVERY_SKILL_NAME = 'financial-factor-discovery' as const;
export const FINANCIAL_FACTOR_PORTFOLIO_SCHEMA = 'deepscientist.financial_factor.portfolio.v1' as const;
export const FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID = 'financial_factor_portfolio' as const;
export const FINANCIAL_FACTOR_PROMPT_CONTRACT_VERSION = '2.0.1' as const;
export type FinancialFactorExecutionMode = 'manual' | 'continuous';
export type FinancialFactorAutomationPolicy = 'verify_only' | 'submit_qualified';
export type FinancialFactorConversationExtra = {
    enabled: true;
    mode: typeof FINANCIAL_FACTOR_RUNTIME_MODE_ID;
    projectRoot?: string;
    focus: 'financial_factor_mining';
    defaultSkill: typeof FINANCIAL_FACTOR_DISCOVERY_SKILL_NAME;
    schema: typeof FINANCIAL_FACTOR_PORTFOLIO_SCHEMA;
    artifactId: typeof FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID;
    executionMode: FinancialFactorExecutionMode;
    automationPolicy: FinancialFactorAutomationPolicy;
    sopVersion: 1;
    rules: {
        userIntentFirst: true;
        avoidFabricatedBacktests: true;
        requireAssumptionLogging: true;
    };
};
/**
 * The policy block deliberately excludes the UI identity, workspace and
 * memory overlays. Those are assembled by each host, while this block stays
 * byte-identical and therefore auditable across UI and headless execution.
 */
export const buildFinancialFactorModePrompt = (projectRoot?: string, _preferredLocale?: string, executionMode: FinancialFactorExecutionMode = 'manual', automationPolicy: FinancialFactorAutomationPolicy = 'verify_only'): string => [
    '# DeepScientist Financial Factor Mining Mode',
    '',
    '- Read `financial-factor-discovery` first. Read `wq-alpha-research` only for the concrete data, evaluation, backtest, export, or submission step selected by the campaign.',
    '- Use the XAlpha-inspired campaign in this order: report-to-memory absorption -> macro mechanism routing -> micro seed/evolution -> deterministic validation -> cross-family review. Preserve source attribution and never treat upstream prompts or paper results as local evidence.',
    `- Execution mode is ${executionMode}; automation policy is ${automationPolicy}. Continuous only permits continuation: it does not imply mine, a costly backtest, promotion, or external submission.`,
    '- In continuous mode, maintain one bounded Campaign in `factor-research/campaign.md` with explicit budget, holdout boundaries, stop criteria, and a factor lineage graph. The final test set never selects candidates.',
    '- Follow the Skill route for explore, validate, compare, mine, export, or submit. `mine` is an Agent-led exploration: choose XAlpha roles or bounded generic roles, dispatch independent worktree branches when useful, combine their handoffs, then run one Lead-owned canonical `factor_lab` evaluation before one `factor_submit` call.',
    '- Keep each retained candidate honest. Metrics are optional and must be measured or explicitly marked pending/literature/estimated; never fill gaps with zero. A useful exploration may be submitted as partial.',
    '- If Team Mode is active, use its injected ds-team factor Lead/Worker contract. The Lead can select XAlpha-inspired roles or create a generic role for data, implementation, review, or visualization; Workers return structured handoffs and never submit directly.',
    '- Complete the user-facing loop with one `factor_submit` call using the canonical evaluationId and persist its canonical result in `factor-research/submissions.json`. The server resolves factor identity, frozen protocol, data snapshot, measured metrics, chart series, result hash, and receipt. Add only optional role activity, limitations, and next actions. Without an evaluation, submit a visible partial risk instead of Agent-supplied measured values.',
    '- Use Git as the research memory only when the authorized project root is a bound Git workspace. Otherwise report Git receipts and commit-based lineage as unavailable; never invent them.',
    '- Record factor ancestry and evaluator details in the candidate artifact when they are known, but do not make lineage fields a prerequisite for a useful first exploration.',
    '- Never fabricate metrics, curves, receipts, status, or verification. Treat verify_only as no unattended external submission.',
    projectRoot
        ? `- Authorized project root: ${projectRoot}`
        : '- No explicit project root was provided; avoid reading unrelated folders unless the user authorizes it.',
    '- Reply in the user language with only: what ran, the current decision, the strongest evidence or blocker, and the next action.',
].join('\n');
export const buildFinancialFactorConversationExtra = (projectRoot?: string, executionMode: FinancialFactorExecutionMode = 'manual', automationPolicy: FinancialFactorAutomationPolicy = 'verify_only'): FinancialFactorConversationExtra => ({
    enabled: true,
    mode: FINANCIAL_FACTOR_RUNTIME_MODE_ID,
    projectRoot,
    focus: 'financial_factor_mining',
    defaultSkill: FINANCIAL_FACTOR_DISCOVERY_SKILL_NAME,
    schema: FINANCIAL_FACTOR_PORTFOLIO_SCHEMA,
    artifactId: FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID,
    executionMode,
    automationPolicy,
    sopVersion: 1,
    rules: {
        userIntentFirst: true,
        avoidFabricatedBacktests: true,
        requireAssumptionLogging: true,
    },
});
