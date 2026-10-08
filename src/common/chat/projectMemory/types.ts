/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */
export const PROJECT_MEMORY_SCHEMA = 'deepscientist.project_memory.v2' as const;
export type ProjectMemoryConversationExtra = {
    schema: typeof PROJECT_MEMORY_SCHEMA;
    enabled: true;
    storage: 'git';
    scope: 'project';
    authority: 'bound-project-git';
    candidateScope: 'conversation';
    readPolicy: 'tracked-current-revision';
    writePolicy: 'bound-project-worktree';
    promotionPolicy: 'verified-checkpoint';
    visibility: 'repository-access';
    root: 'memory';
    categories: [
        'methods',
        'knowledge',
        'lessons'
    ];
    activeModeIds: string[];
};
