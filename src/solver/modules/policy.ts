import { z } from 'zod';

export type ResearchModuleSlot = 'M1' | 'M3' | 'M4' | 'M5';
export type CustomResearchModule = {
  id: string;
  name: string;
  slot: ResearchModuleSlot;
  mode: 'append' | 'replace';
  enabled: boolean;
  instructions: string;
};
export type ResearchModulePlan = {
  scheduler: 'plan' | 'goals-first' | 'critical-path' | 'continuation' | 'primary-led';
  context: 'full' | 'essential';
  custom: CustomResearchModule[];
};

const encoder = new TextEncoder();
const textBytes = (value: string) => encoder.encode(value).byteLength;
const noNul = (value: string) => !value.includes('\0');
const customResearchModuleSchema = z.object({
  id: z.string().regex(/^[A-Za-z0-9_-]{1,64}$/u, '模块 ID 只能包含 1–64 个字母、数字、下划线或连字符。')
    .refine(value => !['__proto__', 'prototype', 'constructor'].includes(value), '请更换模块 ID。'),
  name: z.string().max(40, '模块名称最多 40 个字符。')
    .refine(noNul, '模块名称不能包含空字符。'),
  slot: z.enum(['M1', 'M3', 'M4', 'M5']),
  mode: z.enum(['append', 'replace']),
  enabled: z.boolean(),
  instructions: z.string().max(4_000, '单个模块的规则最多 4,000 字节。')
    .refine(noNul, '模块规则不能包含空字符。')
    .refine(value => textBytes(value) <= 4_000, '单个模块的规则最多 4,000 UTF-8 字节。'),
}).strict();

export const researchModulePlanDraftSchema = z.object({
  scheduler: z.enum(['plan', 'goals-first', 'critical-path', 'continuation', 'primary-led']),
  context: z.enum(['full', 'essential']),
  custom: z.array(customResearchModuleSchema).max(8, '最多添加 8 个自定义模块。'),
}).strict().superRefine((plan, context) => {
  const ids = new Set<string>();
  for (const [index, module] of plan.custom.entries()) {
    if (ids.has(module.id)) context.addIssue({ code: z.ZodIssueCode.custom,
      path: ['custom', index, 'id'], message: '自定义模块 ID 不能重复。' });
    ids.add(module.id);
  }
  if (plan.custom.reduce((bytes, module) => bytes + textBytes(module.instructions), 0) > 16_000)
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['custom'], message: '全部自定义规则最多 16,000 UTF-8 字节。' });
});

export const researchModulePlanSchema = researchModulePlanDraftSchema.superRefine((plan, context) => {
  const replaced = new Set<ResearchModuleSlot>();
  for (const [index, module] of plan.custom.entries()) {
    if (!module.name.trim()) context.addIssue({ code: z.ZodIssueCode.custom,
      path: ['custom', index, 'name'], message: '请填写模块名称。' });
    if (!module.enabled) continue;
    if (!module.instructions.trim()) context.addIssue({ code: z.ZodIssueCode.custom,
      path: ['custom', index, 'instructions'], message: '启用模块前请填写规则。' });
    if (module.mode === 'replace') {
      if (replaced.has(module.slot)) context.addIssue({ code: z.ZodIssueCode.custom,
        path: ['custom', index, 'mode'], message: '每个组件最多启用一个替换模块。' });
      replaced.add(module.slot);
    }
  }
});

export function defaultResearchModulePlan(): ResearchModulePlan {
  return { scheduler: 'plan', context: 'full', custom: [] };
}
