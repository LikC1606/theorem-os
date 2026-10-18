import type { SourceDiffRow } from './sourceDiff';

const html = (value: string) => value.replace(/[&<>"']/g, character => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
}[character]!));

// Both comparisons keep the original text and line identities, including blank lines.
export function sourceDiffRows(rows: readonly SourceDiffRow[]) {
  const seen = new Set<number>();
  const markup = rows.map(row => {
    if (row.kind === 'gap') return `<tr class="diff-gap"><td colspan="3">${row.count} 行未改动</td></tr>`;
    const firstChange = row.changeId !== undefined && !seen.has(row.changeId);
    if (row.changeId !== undefined) seen.add(row.changeId);
    return `<tr class="diff-${row.kind}"${row.oldLine === undefined ? '' : ` data-old-line="${row.oldLine}"`}${row.newLine === undefined ? '' : ` data-new-line="${row.newLine}"`}${firstChange ? ` data-change-start="${row.changeId}"` : ''}>
    <td class="diff-line-no">${row.oldLine ?? ''}</td><td class="diff-line-no">${row.newLine ?? ''}</td><td class="diff-code"><span class="diff-marker" aria-hidden="true">${row.kind === 'added' ? '+' : row.kind === 'removed' ? '-' : ' '}</span><code data-diff-text>${html(row.text)}</code>${row.noNewline ? `<span class="diff-no-newline" data-eof-side="${row.kind === 'removed' ? 'old' : row.kind === 'added' ? 'new' : 'both'}">文件末尾无换行</span>` : ''}</td></tr>`;
  }).join('');
  return { markup, changeCount: seen.size };
}
