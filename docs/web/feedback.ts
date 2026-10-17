import { createIcons, ArrowRight, ArrowUpRight, Bug, Copy, Download, GitFork, Lightbulb, MessageCircle, X } from 'lucide';

createIcons({ icons: { ArrowRight, ArrowUpRight, Bug, Copy, Download, GitFork, Lightbulb, MessageCircle, X }, attrs: { 'aria-hidden': 'true' } });

const element = <T extends HTMLElement = HTMLElement>(id: string): T => {
  const result = document.getElementById(id);
  if (!result) throw new Error(`Missing feedback element: ${id}`);
  return result as T;
};
const issueDestination = 'https://github.com/LikC1606/theorem-os/issues/new';
const kinds = {
  bug: { name: '问题反馈', prefix: '[Bug]', hint: '可附上复现步骤、错误信息与预期结果。', placeholder: '发生了什么？如何复现？你期望的结果是什么？' },
  feature: { name: '功能建议', prefix: '[Feature]', hint: '描述使用场景、希望的改进与它能解决的问题。', placeholder: '你希望增加或改进什么？会在什么场景下使用？' },
  question: { name: '使用咨询', prefix: '[Question]', hint: '描述疑问，以及已经尝试过的方法。', placeholder: '你想了解什么？已经查阅或尝试了哪些方法？' },
};
type Kind = keyof typeof kinds;
const form = element<HTMLFormElement>('feedback-form');
const area = element<HTMLSelectElement>('feedback-area');
const subject = element<HTMLInputElement>('feedback-subject');
const description = element<HTMLTextAreaElement>('feedback-description');
const environment = element<HTMLInputElement>('feedback-environment');
const review = element<HTMLDialogElement>('feedback-review');
const markdown = element<HTMLTextAreaElement>('feedback-markdown');
const github = element<HTMLAnchorElement>('feedback-github');
const status = element('feedback-export-status');
const kindInputs = Array.from(form.querySelectorAll<HTMLInputElement>('input[name="feedback-kind"]'));
const selectedKind = (): Kind => {
  const value = kindInputs.find(input => input.checked)?.value;
  return value && Object.hasOwn(kinds, value) ? value as Kind : 'bug';
};

function updateFields() {
  const kind = kinds[selectedKind()];
  element('feedback-description-hint').textContent = kind.hint;
  description.placeholder = kind.placeholder;
  subject.setCustomValidity(subject.value.trim() ? '' : '请填写反馈标题。');
  description.setCustomValidity(description.value.trim() ? '' : '请填写详细描述。');
  element('feedback-count').textContent = `${description.value.length} / ${description.maxLength}`;
}
form.addEventListener('input', updateFields);
form.addEventListener('change', updateFields);

form.addEventListener('submit', event => {
  event.preventDefault();
  updateFields();
  if (!form.reportValidity()) return;
  const kind = kinds[selectedKind()];
  const title = `${kind.prefix} ${subject.value.trim()}`;
  const body = [
    `### 反馈类型\n${kind.name}`,
    `### 相关位置\n${area.selectedOptions[0]?.textContent ?? area.value}`,
    `### 详细描述\n${description.value.trim()}`,
    ...(environment.value.trim() ? [`### 环境与版本\n${environment.value.trim()}`] : []),
    '---\n来自 TheoremOS 反馈页。',
  ].join('\n\n');
  const destination = new URL(issueDestination);
  destination.searchParams.set('title', title);
  destination.searchParams.set('body', body);
  // Keep the full text available when encoded Unicode or logs exceed a practical URL limit.
  const needsPaste = destination.href.length > 7500;
  if (needsPaste) destination.searchParams.delete('body');
  markdown.value = `# ${title}\n\n${body}\n`;
  element('feedback-review-summary').textContent = title;
  element('feedback-review-note').textContent = needsPaste
    ? '内容较长，请先复制或下载全文，再到 GitHub 粘贴发布。'
    : '将在 GitHub 打开草稿，确认后才会公开发布。截图和附件可在 GitHub 补充。';
  github.href = destination.href;
  status.textContent = '';
  review.showModal();
  markdown.setSelectionRange(0, 0);
  markdown.scrollTop = 0;
  markdown.scrollLeft = 0;
});

element('feedback-review-close').addEventListener('click', () => review.close());
review.addEventListener('close', () => element('feedback-preview').focus({ preventScroll: true }));

element('feedback-copy').addEventListener('click', async () => {
  try {
    await navigator.clipboard.writeText(markdown.value);
    status.textContent = '已复制反馈全文。';
  } catch {
    markdown.focus();
    markdown.select();
    status.textContent = '未能自动复制，已选中全文，可手动复制。';
  }
});
element('feedback-download').addEventListener('click', () => {
  const objectUrl = URL.createObjectURL(new Blob([markdown.value], { type: 'text/markdown;charset=utf-8' }));
  const link = document.createElement('a');
  link.href = objectUrl;
  link.download = 'theoremos-feedback.md';
  link.click();
  setTimeout(() => URL.revokeObjectURL(objectUrl), 1000);
  status.textContent = '已准备反馈 Markdown 下载。';
});

updateFields();
form.hidden = false;
element('feedback-fallback').hidden = true;
document.documentElement.dataset.feedbackReady = 'true';
