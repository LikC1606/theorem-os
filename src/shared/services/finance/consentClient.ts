import fs from 'node:fs/promises';
import type { FinanceConsentGrant } from "../../../common/chat/finance/index";
import {
  BUILTIN_USER_INPUT_GATEWAY_STATE_ENV,
  parseBuiltinUserInputGatewayState,
  resolveBuiltinUserInputGatewayStatePath,
} from "../../../mcp/constants";
import { FinanceRuntimeError } from "./client";

type ConsentExpectation = {
  runId: string;
  consentScope: FinanceConsentGrant['consentScope'];
  action: string;
  resourceId?: string;
  disclosureHash?: string;
};

export async function consumeFinanceConsent(
  grant: FinanceConsentGrant | undefined,
  expectation: ConsentExpectation
): Promise<void> {
  if (!grant) throw new FinanceRuntimeError('permission_denied', 'Explicit user consent is required.');
  const statePath = resolveBuiltinUserInputGatewayStatePath(process.env[BUILTIN_USER_INPUT_GATEWAY_STATE_ENV]);
  let state;
  try {
    state = parseBuiltinUserInputGatewayState(JSON.parse(await fs.readFile(statePath, 'utf8')));
  } catch {
    state = undefined;
  }
  if (!state) throw new FinanceRuntimeError('permission_denied', 'The consent gateway is unavailable.');
  const endpoint = new URL(state.url);
  endpoint.pathname = '/finance-consent/consume';
  endpoint.search = '';
  endpoint.hash = '';
  const response = await fetch(endpoint, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', Authorization: `Bearer ${state.token}` },
    body: JSON.stringify({
      consentId: grant.consentId,
      decisionToken: grant.decisionToken,
      runId: expectation.runId,
      consentScope: expectation.consentScope,
      action: expectation.action,
      resourceId: expectation.resourceId,
      disclosureHash: expectation.disclosureHash,
      confirmationHash: grant.confirmationHash,
    }),
  });
  if (!response.ok) {
    throw new FinanceRuntimeError('permission_denied', 'The finance consent is missing, expired, mismatched, or used.');
  }
  const result = (await response.json()) as { ok?: boolean };
  if (result.ok !== true)
    throw new FinanceRuntimeError('permission_denied', 'The finance consent could not be verified.');
}
