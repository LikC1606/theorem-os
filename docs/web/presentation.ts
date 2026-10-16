import type { ArchiveCatalog } from './types';

const escape = (value: string) => value.replace(/[&<>"']/g, character => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
}[character]!));

/** A mathematical illustration, separate from the archived proof and its evidence. */
export function researchManifold() {
  type Vector = [number, number, number];
  const normalize = (v: Vector): Vector => {
    const length = Math.hypot(...v);
    return v.map(value => value / length) as Vector;
  };
  const cross = (a: Vector, b: Vector): Vector => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const rotate = ([x, y, z]: Vector): Vector => {
    const a = -.42, b = .64, c = -.22;
    const yy = y * Math.cos(a) - z * Math.sin(a), zz = y * Math.sin(a) + z * Math.cos(a);
    const xx = x * Math.cos(b) + zz * Math.sin(b), zzz = -x * Math.sin(b) + zz * Math.cos(b);
    return [xx * Math.cos(c) - yy * Math.sin(c), xx * Math.sin(c) + yy * Math.cos(c), zzz];
  };
  const vertex = (u: number, v: number) => {
    const center: Vector = [54 * (Math.sin(u) + 2 * Math.sin(2 * u)), 54 * (Math.cos(u) - 2 * Math.cos(2 * u)), -57 * Math.sin(3 * u)];
    const tangent = normalize([Math.cos(u) + 4 * Math.cos(2 * u), -Math.sin(u) + 4 * Math.sin(2 * u), -3 * Math.cos(3 * u)]);
    const normal = normalize(cross(tangent, Math.abs(tangent[2]) > .92 ? [0, 1, 0] : [0, 0, 1]));
    const binormal = cross(tangent, normal);
    const outward = normal.map((value, i) => value * Math.cos(v) + binormal[i] * Math.sin(v)) as Vector;
    return { point: rotate(center.map((value, i) => value + 27 * outward[i]) as Vector), normal: rotate(outward) };
  };
  const project = ([x, y, z]: Vector) => {
    const perspective = 850 / (850 - z) * 1.22;
    return `${(320 + x * perspective).toFixed(1)},${(265 + y * perspective).toFixed(1)}`;
  };
  const faces: { depth: number; markup: string }[] = [];
  const steps = 180, sides = 28;
  const light = normalize([-.4, -.65, .9]);
  for (let i = 0; i < steps; i++) for (let j = 0; j < sides; j++) {
    const u = i / steps * Math.PI * 2, v = j / sides * Math.PI * 2;
    const du = Math.PI * 2 / steps, dv = Math.PI * 2 / sides;
    const corners = [vertex(u, v), vertex(u + du, v), vertex(u + du, v + dv), vertex(u, v + dv)];
    const { normal } = vertex(u + du / 2, v + dv / 2);
    const diffuse = Math.max(0, normal.reduce((sum, value, axis) => sum + value * light[axis], 0));
    const rim = Math.pow(1 - Math.abs(normal[2]), 3);
    const specular = Math.pow(diffuse, 12);
    const channel = (base: number, spread: number) => Math.min(255, Math.round(base + spread * diffuse + rim * 24 + specular * 50));
    const color = `rgb(${channel(22, 70)},${channel(53, 115)},${channel(136, 105)})`;
    faces.push({ depth: corners.reduce((sum, corner) => sum + corner.point[2], 0) / 4,
      markup: `<path d="M${corners.map(corner => project(corner.point)).join('L')}Z" fill="${color}" stroke="${color}" stroke-width=".7"/>` });
  }
  const orbit = 'M65,292a255,145 0 1,0 510,0a255,145 0 1,0-510,0';
  return `<g class="manifold-wire">${faces.sort((a, b) => a.depth - b.depth).map(face => face.markup).join('')}</g><path class="manifold-route" d="${orbit}"/><path class="manifold-pulse" d="${orbit}"/>`;
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
