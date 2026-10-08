/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type { MedicalEvidenceConfig } from "../config/storage";

export type MedicalEvidencePaperclipSource = NonNullable<MedicalEvidenceConfig['defaultSources']>[number];

export const MEDICAL_EVIDENCE_DEFAULT_PAPERCLIP_SOURCES: MedicalEvidencePaperclipSource[] = [
  'pmc',
  'abstracts',
  'abstracts_only',
  'biorxiv',
  'medrxiv',
  'arxiv',
  'fda',
  'fda/eu',
  'fda/jp',
  'trials',
  'trials/us',
  'clinicaltrials',
  'trials/cn',
  'trials/eu',
  'trials/jp',
];

export const MEDICAL_EVIDENCE_PAPERCLIP_SOURCE_GROUPS: Array<{
  id: string;
  label: string;
  intent: string;
  sources: MedicalEvidencePaperclipSource[];
}> = [
  {
    id: 'full_text_and_abstracts',
    label: '论文全文与摘要',
    intent: '优先支撑疗效、诊断、预后和机制证据，全文锚点优先于摘要。',
    sources: ['pmc', 'abstracts', 'abstracts_only'],
  },
  {
    id: 'preprints',
    label: '预印本',
    intent: '用于前沿线索和新兴证据，默认不得压过指南、说明书、系统综述或成熟 RCT。',
    sources: ['biorxiv', 'medrxiv', 'arxiv'],
  },
  {
    id: 'regulatory_labels',
    label: '监管与药品说明',
    intent: '药物安全、适应证、剂量、禁忌和特殊人群问题必须优先检查。',
    sources: ['fda', 'fda/eu', 'fda/jp'],
  },
  {
    id: 'trial_registries',
    label: '临床试验注册',
    intent: '用于在研证据、研究状态、样本量和未发表结果背景，不等同于已发表结论。',
    sources: ['trials', 'trials/us', 'clinicaltrials', 'trials/cn', 'trials/eu', 'trials/jp'],
  },
];

export const MEDICAL_EVIDENCE_EVIDENCE_HIERARCHY = [
  {
    rank: 1,
    label: '当前指南 / 共识 / 监管说明书',
    confidence: 'high',
    rule: '当问题涉及药物安全、适应证、剂量、禁忌、妊娠、儿童或复杂合并症时，药品说明书和监管来源优先级最高。',
  },
  {
    rank: 2,
    label: '系统综述 / Meta 分析',
    confidence: 'high',
    rule: '优先采用近年、方法透明、异质性可解释且人群匹配的综述；若纳入研究过旧或间接，应降级。',
  },
  {
    rank: 3,
    label: '随机对照试验（RCT）',
    confidence: 'high/moderate',
    rule: '样本量充分、终点临床相关、人群和干预匹配时可作为高质量证据；开放标签、小样本或替代终点需降级。',
  },
  {
    rank: 4,
    label: '前瞻性队列 / 高质量真实世界研究',
    confidence: 'moderate',
    rule: '适合安全性、预后、罕见结局和长期随访问题；存在混杂和选择偏倚时降级。',
  },
  {
    rank: 5,
    label: '病例对照 / 病例系列 / 注册库摘要',
    confidence: 'low',
    rule: '主要用于线索、风险信号或罕见情境，不能单独支撑强治疗建议。',
  },
  {
    rank: 6,
    label: '预印本 / 会议摘要 / 机制推断',
    confidence: 'low/very_low',
    rule: '仅作前沿补充；未同行评议、未完整发表或仅机制外推时必须明确限制。',
  },
] as const;

export const MEDICAL_EVIDENCE_SOURCE_TIER_RULES = [
  'Tier A: 指南、监管/药品说明、顶级或权威期刊的系统综述/RCT；可作为主要依据，但仍需人群匹配和锚点。',
  'Tier B: 专科期刊 RCT、方法稳健的队列研究、真实世界研究；通常作为支持证据或适用性补充。',
  'Tier C: 注册库、摘要、预印本、病例系列、机制研究；用于线索和背景，默认不能单独决定临床结论。',
  '期刊层级不是唯一标准。NEJM、Lancet、JAMA、BMJ、Nature Medicine、Annals、权威专科指南等可标记 leading_journal，但仍需检查研究设计、样本、终点和适用人群。',
  '若高层级证据与低层级证据方向不同，默认采纳高层级且人群更匹配、更新、锚点更完整的来源；低层级证据写入局限或待验证。',
] as const;

export const normalizeMedicalEvidenceSources = (sources?: string[]): MedicalEvidencePaperclipSource[] => {
  const selected = sources?.length ? sources : MEDICAL_EVIDENCE_DEFAULT_PAPERCLIP_SOURCES;
  const normalized = selected.map((source) => (source === 'clinicaltrials' ? 'trials/us' : source));
  const unique = [...new Set(normalized)].filter((source): source is MedicalEvidencePaperclipSource =>
    MEDICAL_EVIDENCE_DEFAULT_PAPERCLIP_SOURCES.includes(source as MedicalEvidencePaperclipSource)
  );
  return unique.length ? unique : MEDICAL_EVIDENCE_DEFAULT_PAPERCLIP_SOURCES;
};
