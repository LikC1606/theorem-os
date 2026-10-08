/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
import type { AcpInitializeResult, AcpSessionConfigOption, AcpSessionModes } from "../types/platform/acpTypes";
import type { SpeechToTextConfig } from "../types/provider/speech";
import type { BetaTestingConfig } from "./betaTesting";
import type { ICssTheme, IMcpServer, AlphaDojoFinanceConfig, MedicalEvidenceConfig, ResearchEvidenceConfig, ScienceArtifactConfig, TProviderWithModel, } from "./storage";
import type { Theme } from "../theme/types";
import type { ComputeConfig } from "../types/compute";
import type { NetworkProxyConfig } from "./networkProxy";
import type { BiomedicalExecutionConfig } from "./biomedicalExecution";
import type { PetActivityMotion } from "../types/platform/petActivity";
import type { IoaiCompetitionAgentPoolConfig } from "../chat/ioaiCompetition";
import type { DeepScientistTeamConfig } from "../chat/team/deepScientistTeam";
import type { PerformanceProfile } from "./performanceProfile";
export type ConfigKeyMap = {
    'google.config': {
        proxy?: string;
    };
    'codex.config': {
        cli_path?: string;
        yoloMode?: boolean;
        sandboxMode?: 'read-only' | 'workspace-write' | 'danger-full-access';
    } | undefined;
    'acp.config': {
        [backend: string]: {
            auth_methodId?: string;
            authToken?: string;
            lastAuthTime?: number;
            cli_path?: string;
            yoloMode?: boolean;
            preferredMode?: string;
            preferredModelId?: string;
            preferredThoughtLevel?: string;
            promptTimeout?: number;
        };
    };
    'acp.promptTimeout': number | undefined;
    'acp.agentIdleTimeout': number | undefined;
    'acp.cachedInitializeResult': Record<string, AcpInitializeResult> | undefined;
    'acp.cached_config_options': Record<string, AcpSessionConfigOption[]> | undefined;
    'acp.cachedModes': Record<string, AcpSessionModes> | undefined;
    'mcp.config': IMcpServer[];
    language: string;
    theme: string;
    colorScheme: string;
    'ui.zoomFactor': number | undefined;
    'ui.fontSize.chat': number | undefined;
    'ui.fontSize.markdown': number | undefined;
    'ui.fontSize.code': number | undefined;
    'window.bounds': {
        x?: number;
        y?: number;
        width: number;
        height: number;
    } | undefined;
    'webui.desktop.enabled': boolean | undefined;
    'webui.desktop.allowRemote': boolean | undefined;
    'webui.desktop.port': number | undefined;
    'network.proxy': NetworkProxyConfig | undefined;
    customCss: string;
    'css.themes': ICssTheme[];
    'css.activeThemeId': string;
    'theme.activeId': string;
    'theme.userThemes': Theme[];
    'tools.imageGenerationModel': TProviderWithModel & {
        switch?: boolean;
    };
    'tools.medicalEvidence': MedicalEvidenceConfig | undefined;
    'tools.researchEvidence': ResearchEvidenceConfig | undefined;
    'tools.scienceArtifact': ScienceArtifactConfig | undefined;
    'tools.alphaDojoFinance': AlphaDojoFinanceConfig | undefined;
    'tools.biomedicalExecution': BiomedicalExecutionConfig | undefined;
    'tools.compute': ComputeConfig | undefined;
    'tools.speechToText': SpeechToTextConfig | undefined;
    'features.betaTesting': BetaTestingConfig | undefined;
    'modes.enabled': Record<string, boolean> | undefined;
    'modes.defaultPrimary': string | undefined;
    'challenge.agentPool': IoaiCompetitionAgentPoolConfig | undefined;
    'team.agentPool': DeepScientistTeamConfig | undefined;
    'workspace.pasteConfirm': boolean | undefined;
    /** Default root for new projects in standalone WebUI. */
    'workspace.defaultRoot': string | undefined;
    'upload.saveToWorkspace': boolean | undefined;
    'guid.lastSelectedAgent': string | undefined;
    'system.closeToTray': boolean | undefined;
    'system.notificationEnabled': boolean | undefined;
    'system.cronNotificationEnabled': boolean | undefined;
    'system.keepAwake': boolean | undefined;
    'system.autoPreviewOfficeFiles': boolean | undefined;
    'system.performanceProfile': PerformanceProfile | undefined;
    'telemetry.updateEnabled': boolean | undefined;
    'telemetry.usageEnabled': boolean | undefined;
    'telemetry.diagnosticsEnabled': boolean | undefined;
    'assistant.telegram.defaultModel': {
        id: string;
        use_model: string;
    } | undefined;
    'assistant.telegram.agent': {
        agent_type: string;
        backend?: string;
        id?: string;
        custom_agent_id?: string;
        name?: string;
    } | undefined;
    'assistant.lark.defaultModel': {
        id: string;
        use_model: string;
    } | undefined;
    'assistant.lark.agent': {
        agent_type: string;
        backend?: string;
        id?: string;
        custom_agent_id?: string;
        name?: string;
    } | undefined;
    'assistant.dingtalk.defaultModel': {
        id: string;
        use_model: string;
    } | undefined;
    'assistant.dingtalk.agent': {
        agent_type: string;
        backend?: string;
        id?: string;
        custom_agent_id?: string;
        name?: string;
    } | undefined;
    'assistant.weixin.defaultModel': {
        id: string;
        use_model: string;
    } | undefined;
    'assistant.weixin.agent': {
        agent_type: string;
        backend?: string;
        id?: string;
        custom_agent_id?: string;
        name?: string;
    } | undefined;
    'assistant.wecom.defaultModel': {
        id: string;
        use_model: string;
    } | undefined;
    'assistant.wecom.agent': {
        agent_type: string;
        backend?: string;
        id?: string;
        custom_agent_id?: string;
        name?: string;
    } | undefined;
    'skillsMarket.enabled': boolean | undefined;
    'pet.enabled': boolean | undefined;
    'pet.size': number | undefined;
    'pet.style': 'deepscientist' | 'classic' | 'paperfold' | 'observatory' | undefined;
    'pet.personality': 'calm' | 'balanced' | 'lively' | undefined;
    'pet.dnd': boolean | undefined;
    'pet.confirmEnabled': boolean | undefined;
    'pet.activityEnabled': boolean | undefined;
    'pet.activityCount': 1 | 3 | undefined;
    'pet.motion': PetActivityMotion | undefined;
    // One-shot completion flags for legacy → backend migrations. Kept in the
    // local config file (not the backend client-preferences bag) so a downgrade
    // to a pre-flag build still re-reads the legacy data unchanged. See
    // `migrateProviders` / `migrateAssistantsToBackend` (ELECTRON-1KT).
    'migration.providersMigrated_v1': boolean | undefined;
    'migration.assistantsMigrated_v1': boolean | undefined;
};
