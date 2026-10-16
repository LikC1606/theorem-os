import type { ArchiveCatalog } from './types';

const escape = (value: string) => value.replace(/[&<>"']/g, character => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
}[character]!));

const artworks: Record<string, string> = {
  annals_equiangular_lines_fixed_angle: `<svg viewBox="0 0 300 145" aria-hidden="true"><g class="proof-lines"><path d="M34 109 263 34M58 26 243 118M150 8 150 137M30 73 274 73M71 127 227 15M58 17 246 131"/><circle cx="150" cy="73" r="45"/><circle cx="150" cy="73" r="65" stroke-dasharray="2 6"/></g><path d="M191 58A44 44 0 0 1 194 73" class="proof-accent"/><circle cx="150" cy="73" r="4" class="proof-dot"/><text x="207" y="65">α</text></svg>`,
  annals_rademacher_enflo_type: `<div class="type-formula" role="img" aria-label="T R 小于等于 T E 小于等于 pi 除以根号 2 乘 T R"><span>T<sub>R</sub></span><b>≤</b><span>T<sub>E</sub></span><b>≤</b><span class="formula-fraction"><span>π</span><span>√2</span></span><span>T<sub>R</sub></span></div><span class="formula-domain">1 ≤ p ≤ 2 · Banach space X</span>`,
  annals_unit_conjecture: `<div class="unit-formula"><span>u</span><span class="formula-times">·</span><span>u<sup>−1</sup></span><span class="formula-equals">=</span><span>1</span></div><span class="formula-domain">Non-trivial units · Group rings</span>`,
};

export function acceptedProofCards(catalog: ArchiveCatalog) {
  return catalog.records.filter(record => record.status === 'official_accepted').map((record, index) => `
    <article class="proof-card" data-accepted-proof="${record.id}">
      <div class="proof-card-top"><span class="mono">0${index + 1} / ${escape(record.area)}</span><span class="proof-pass"><i data-lucide="check"></i>Official pass</span></div>
      <div class="proof-art">${artworks[record.id] ?? '<span class="unit-formula">⊢</span>'}</div>
      <div class="proof-card-body"><p class="proof-subtitle">${escape(record.subtitle)}</p><h3><a href="archive.html#proof=${record.id}">${escape(record.title)}</a></h3><p class="proof-credit">${escape(record.model)}</p></div>
      <div class="proof-card-footer"><a href="archive.html#proof=${record.id}&tab=source">查看证明<i data-lucide="arrow-right"></i></a><a class="official-link" href="${escape(record.official!.resultUrl)}" target="_blank" rel="noreferrer" aria-label="${escape(record.title)} 官方验收记录">官方验收<i data-lucide="arrow-up-right"></i></a></div>
    </article>`).join('');
}

type ReplayEvidence = {
  schema: string; status: string; source: string; modelInvoked: boolean; official: boolean; checkedAt: string;
  targets: { theorem: string; declaration: string; status: string; sorryCount: number }[];
};

function leanCode(source: string) {
  return source.trimEnd().split('\n').map((line, index) => {
    let cursor = 0;
    let markup = '';
    for (const match of line.matchAll(/\b(namespace|theorem|by|end|exact|rfl|Nat)\b/g)) {
      markup += escape(line.slice(cursor, match.index)) + `<span class="syntax-${match[0] === 'Nat' ? 'type' : 'keyword'}">${match[0]}</span>`;
      cursor = match.index! + match[0].length;
    }
    markup += escape(line.slice(cursor));
    return `<span class="code-line${line.includes('exact Nat.zero_add') ? ' is-change' : ''}" data-line="${index + 1}">${markup || '&#8203;'}</span>`;
  }).join('');
}

/** Sources come from the bundled tutorial; the final receipt comes from the recorded local replay. */
export function researchReplay(failedSource: string, proofSource: string, evidence: ReplayEvidence) {
  if (evidence.schema !== 'theoremos.site-replay-evidence.v1' || evidence.source !== 'preset-replay' ||
      evidence.modelInvoked !== false || evidence.official !== false || evidence.status !== 'evaluated_passed' ||
      evidence.targets.length !== 2 || !evidence.targets.every(target => target.status === 'kernel_verified' && target.sorryCount === 0)) {
    throw new Error('The website replay needs a recorded, model-free local verification.');
  }
  const stages = [
    { id: 'candidate', label: '候选证明', file: 'Submission.lean', note: '预设候选 01', code: failedSource },
    { id: 'feedback', label: 'Lean 反馈', file: 'Lean feedback', note: '检查过程讲解', code: '' },
    { id: 'repair', label: '修复候选', file: 'Submission.lean', note: '预设候选 02', code: proofSource },
    { id: 'verified', label: '完整原题验收', file: 'Submission.lean', note: '验收源码', code: proofSource },
  ];
  const feedback = `<div class="demo-diagnostic"><span class="diagnostic-label"><i data-lucide="info"></i>对预设候选的检查说明</span><h3>一处通过，<br>一处还需继续。</h3><p><code>add_zero</code> 可由 <code>rfl</code> 完成；<br><code>zero_add</code> 需要已有引理。</p><pre><code>n : Nat\n⊢ 0 + n = n</code></pre><p class="diagnostic-hint">下一份候选使用 <code>Nat.zero_add n</code>。</p></div>`;
  return `<div class="replay-window">
    <div class="replay-chrome"><span class="window-dots" aria-hidden="true"><i></i><i></i><i></i></span><span class="mono">theoremos / local-replay</span><span class="replay-badge"><span class="status-dot"></span>预设回放 · 不调用模型</span></div>
    <div class="replay-tabs" role="tablist" aria-label="预设回放的四个步骤">${stages.map((stage, index) => `<button type="button" role="tab" id="demo-${stage.id}" aria-controls="stage-${stage.id}" aria-selected="${stage.id === 'verified'}" tabindex="${stage.id === 'verified' ? '0' : '-1'}" data-replay-stage="${stage.id}"><span class="mono">0${index + 1}</span><span>${stage.label}</span><i data-lucide="${stage.id === 'verified' ? 'shield-check' : 'arrow-right'}"></i></button>`).join('')}</div>
    <div class="replay-layout"><div class="replay-editor">${stages.map(stage => `<div class="replay-panel" id="stage-${stage.id}" role="tabpanel" aria-labelledby="demo-${stage.id}" tabindex="0"${stage.id === 'verified' ? '' : ' hidden'}><div class="editor-heading"><span><i data-lucide="file-code-2"></i>${stage.file}</span><span>${stage.note}</span></div>${stage.code ? `<pre class="demo-code"><code>${leanCode(stage.code)}</code></pre>` : feedback}</div>`).join('')}</div>
    <aside class="replay-receipt" aria-label="已归档回放的最终验收"><div class="receipt-title"><i data-lucide="shield-check"></i><span>已归档的最终验收</span><span class="receipt-local">LOCAL</span></div><div class="receipt-status"><span class="receipt-check"><i data-lucide="check"></i></span><div><strong>完整原题，通过。</strong><code>${escape(evidence.status)}</code></div></div><div class="receipt-targets">${evidence.targets.map(target => `<div><i data-lucide="check"></i><span><strong>${escape(target.theorem)}</strong><code>${escape(target.declaration.replace(target.theorem + ' ', ''))}</code></span></div>`).join('')}</div><dl class="receipt-facts"><div><dt>验收方式</dt><dd>独立 Lean 内核检查</dd></div><div><dt>sorryCount</dt><dd>${evidence.targets.reduce((sum, target) => sum + target.sorryCount, 0)}</dd></div><div><dt>检查日期</dt><dd>${escape(evidence.checkedAt.slice(0, 10))} UTC</dd></div></dl><a href="archive.html#view=quickstart" class="receipt-link">查看完整回放记录<i data-lucide="arrow-up-right"></i></a></aside></div>
    <div class="replay-caption"><span>预设示例 · 已归档的最终回执 · 非实时运行</span><a href="https://github.com/LikC1606/theorem-os/blob/main/src/math/localExample.ts" target="_blank" rel="noreferrer">预设源码<i data-lucide="arrow-up-right"></i></a></div>
  </div>`;
}
