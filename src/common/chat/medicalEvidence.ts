/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
export const MEDICAL_EVIDENCE_MODE_ID = 'medical_evidence';
export const MEDICAL_EVIDENCE_FIGURE_SKILL_NAME = 'research-figure-diagram';
export const MEDICAL_EVIDENCE_FIGURE_SKILL_PATH = 'resources/skills/research-figure-diagram/SKILL.md';
export const MEDICAL_EVIDENCE_REPORT_CHART_SKILL_NAME = 'deepscientist-report-chart';
export const MEDICAL_EVIDENCE_REPORT_CHART_SKILL_PATH = 'resources/skills/report-chart/SKILL.md';
export const MEDICAL_EVIDENCE_WRITING_SKILL_NAME = 'draft-to-top-conference-oral';
export const MEDICAL_EVIDENCE_WRITING_SKILL_PATH = 'resources/skills/draft-to-top-conference-oral/SKILL.md';
export interface MedicalEvidenceConversationExtra {
    enabled: true;
    mode: typeof MEDICAL_EVIDENCE_MODE_ID;
    report: {
        enabled: true;
        render: 'inline_structured';
        figures: true;
        drawioPreview: true;
    };
    paperclip: {
        enabled: true;
        sources: string[];
        strictAnchors: boolean;
    };
    figureSkill: {
        enabled: true;
        name: typeof MEDICAL_EVIDENCE_FIGURE_SKILL_NAME;
        path: typeof MEDICAL_EVIDENCE_FIGURE_SKILL_PATH;
        useWhen: 'clinical_report_needs_visual_evidence';
    };
    reportChartSkill: {
        enabled: true;
        name: typeof MEDICAL_EVIDENCE_REPORT_CHART_SKILL_NAME;
        path: typeof MEDICAL_EVIDENCE_REPORT_CHART_SKILL_PATH;
        useWhen: 'clinical_report_needs_standard_evidence_chart';
    };
    writingSkill: {
        enabled: true;
        name: typeof MEDICAL_EVIDENCE_WRITING_SKILL_NAME;
        path: typeof MEDICAL_EVIDENCE_WRITING_SKILL_PATH;
        useWhen: 'clinical_report_needs_reader_onboarding_or_editorial_structure';
    };
    sopVersion: 3;
}
