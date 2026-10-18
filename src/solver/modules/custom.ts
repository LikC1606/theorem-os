import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';
import { configuredSolverModules, directSolverModules, type SolverModules } from './index';
import { researchModulePlanSchema, type ResearchModulePlan, type ResearchModuleSlot } from './policy';

export function configurableSolverModules(plan?: ResearchModulePlan,
  coordination: 'cooperative' | 'independent' = 'cooperative', workers = 4): SolverModules {
  if (plan === undefined) return directSolverModules;
  if (!['cooperative', 'independent'].includes(coordination)) throw new Error('math_module_invalid_coordination');
  if (!Number.isSafeInteger(workers) || workers < 1 || workers > 4) throw new Error('math_module_invalid_workers');
  const configuration = researchModulePlanSchema.parse(plan) as ResearchModulePlan;
  const base = configuredSolverModules('direct', configuration.scheduler);
  const rules = configuration.custom.filter(module => module.enabled &&
    (module.slot !== 'M5' || coordination === 'cooperative' && workers > 1));
  if (!rules.length && configuration.context === 'full') return base;
  const digest = mathDigest(canonicalMathJson({ schema: 'theorem-os.research-module-plan.v1',
    scheduler: configuration.scheduler, context: configuration.context, custom: rules }));
  const version = (slot: Exclude<ResearchModuleSlot, 'M4'>) => {
    const selected = rules.filter(module => module.slot === slot);
    return selected.length ? `${base[slot].version}/custom-rules-v1:${mathDigest(canonicalMathJson(selected))}` : base[slot].version;
  };
  return { ...base, id: `${base.id}/custom-plan-v1:${digest}`,
    M1: { ...base.M1, version: version('M1') },
    M3: { ...base.M3, version: version('M3') },
    M5: { ...base.M5, version: version('M5') },
    M4: { ...base.M4, version: `${base.M4.version}/custom-context-v1:${digest}`,
      build: (problem, state, access) => {
        const applied = rules.filter(module => module.slot !== 'M5' || Boolean(state.cooperation));
        const context = base.M4.build(problem, state, { ...access, customModuleRules: applied,
          ...(configuration.context === 'essential' ? { maxOptionalContextBytes: 0 } : {}) });
        if (context.manifest) for (const module of applied) console.log(JSON.stringify({
          event: 'custom_module_applied', at: Date.now(), moduleId: module.id, slot: module.slot, mode: module.mode,
        }));
        return context;
      },
    },
  };
}
