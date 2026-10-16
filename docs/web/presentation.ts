import type { ArchiveCatalog } from './types';

const escape = (value: string) => value.replace(/[&<>"']/g, character => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
}[character]!));

/** A mathematical illustration, separate from the archived proof and its evidence. */
export function researchManifold() {
  const project = (u: number, v: number) => {
    const radius = 146 + 67 * Math.cos(v);
    const x = radius * Math.cos(u), y = radius * Math.sin(u), z = 67 * Math.sin(v);
    const tilt = 1.04;
    const yy = y * Math.cos(tilt) - z * Math.sin(tilt);
    const angle = -0.38;
    return [320 + x * Math.cos(angle) - yy * Math.sin(angle), 282 + x * Math.sin(angle) + yy * Math.cos(angle)];
  };
  const path = (sample: (t: number) => number[], count: number) => Array.from({ length: count + 1 }, (_, i) => {
    const [x, y] = sample(i / count * Math.PI * 2);
    return `${i ? 'L' : 'M'}${x.toFixed(2)},${y.toFixed(2)}`;
  }).join(' ');
  const rings = Array.from({ length: 32 }, (_, i) => `<path d="${path(t => project(i / 32 * Math.PI * 2, t), 70)}"/>`);
  const parallels = Array.from({ length: 20 }, (_, i) => `<path d="${path(t => project(t, i / 20 * Math.PI * 2), 130)}"/>`);
  const trace = path(t => project(t * 2, t * 3), 320);
  const nodes = Array.from({ length: 5 }, (_, i) => {
    const [x, y] = project(i / 5 * Math.PI * 2 + 0.3, i / 5 * Math.PI * 6 + 0.4);
    return `<circle cx="${x.toFixed(2)}" cy="${y.toFixed(2)}" r="4" class="manifold-node"/>`;
  });
  return `<g class="manifold-wire">${rings.join('')}${parallels.join('')}</g><path class="manifold-route" d="${trace}"/><path class="manifold-pulse" d="${trace}"/>${nodes.join('')}`;
}

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
