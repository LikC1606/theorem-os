import {
  mathematicsResearchPolicy,
  MATHEMATICS_RESEARCH_POLICY_ENV,
} from "../common/chat/team/mathematicsResearchPolicy";
import { readMathRunHistoryIdentity } from "./mathRunHistory";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";

export function readMathResearchPolicy(env: NodeJS.ProcessEnv = process.env) {
  const value = resolveMathematicsRuntimeEnvironment(env)[MATHEMATICS_RESEARCH_POLICY_ENV];
  if (value === undefined) return undefined;
  if (!readMathRunHistoryIdentity(env)) throw new Error('Research policy requires frozen managed run inputs.');
  return mathematicsResearchPolicy(value);
}
