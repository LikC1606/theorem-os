/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */
export type SpeechToTextProvider = 'openai' | 'deepgram';
export type OpenAISpeechToTextConfig = {
    api_key: string;
    base_url?: string;
    language?: string;
    model: string;
    prompt?: string;
    temperature?: number;
};
export type DeepgramSpeechToTextConfig = {
    api_key: string;
    base_url?: string;
    detectLanguage?: boolean;
    language?: string;
    model: string;
    punctuate?: boolean;
    smartFormat?: boolean;
};
export type SpeechToTextConfig = {
    autoSend?: boolean;
    enabled: boolean;
    provider: SpeechToTextProvider;
    deepgram?: DeepgramSpeechToTextConfig;
    openai?: OpenAISpeechToTextConfig;
};
