/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */
export type ComputeSshAuthType = 'password' | 'privateKey' | 'agent';
export type ComputeSshHostTestStatus = 'untested' | 'testing' | 'connected' | 'failed';
export type ComputeSshHostTestResult = {
    ok: boolean;
    status: ComputeSshHostTestStatus;
    message: string;
    testedAt: number;
    latencyMs?: number;
    username?: string;
    cwd?: string;
    system?: string;
    gpuSummary?: string[];
};
export type ComputeSshHostConfig = {
    id: string;
    name: string;
    host: string;
    port: number;
    username: string;
    authType: ComputeSshAuthType;
    passwordSecret?: string;
    privateKeyPath?: string;
    privateKeyPassphraseSecret?: string;
    remoteWorkdir?: string;
    tags?: string[];
    notes?: string;
    exposeCredentialsToAgent?: boolean;
    createdAt: number;
    updatedAt: number;
    lastTest?: ComputeSshHostTestResult;
};
export type ComputeConfig = {
    sshHosts?: ComputeSshHostConfig[];
};
export type ComputeSshHostContextHost = {
    id: string;
    name: string;
    host: string;
    port: number;
    username: string;
    authType: ComputeSshAuthType;
    remoteWorkdir?: string;
    tags?: string[];
    notes?: string;
    lastTest?: ComputeSshHostTestResult;
    credentialHint: string;
    password?: string;
    privateKeyPath?: string;
    privateKeyPassphrase?: string;
};
export type ComputeConversationExtra = {
    selected_ssh_host_ids: string[];
    ssh_hosts: Array<Pick<ComputeSshHostContextHost, 'id' | 'name' | 'host' | 'port' | 'username' | 'authType' | 'remoteWorkdir' | 'tags' | 'lastTest'> & {
        credentialHint: string;
    }>;
};
