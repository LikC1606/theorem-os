/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
export const LAB_SKILL_DEPOSITION_MODE_ID = 'lab_skill_deposition';
export interface LabSkillDepositionConversationExtra {
    enabled: true;
    mode: typeof LAB_SKILL_DEPOSITION_MODE_ID;
    projectRoot?: string;
    conversationId?: string;
    sopVersion: 1;
    tool: {
        name: 'lab_skill';
        singleSurface: true;
    };
    report: {
        enabled: true;
        render: 'inline_structured';
        requiresUserEnable: true;
    };
    storage: {
        root: '.deepscientist/skill-deposition';
        draftRoot: '.deepscientist/skill-deposition/sessions';
        skillRoot: '.deepscientist/lab-skills';
    };
}
