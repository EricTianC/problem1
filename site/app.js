const $ = (id) => document.getElementById(id);
const prompt = $('prompt');
const copy = $('copy');

async function readJson(name) {
  const response = await fetch(name);
  if (!response.ok) throw new Error(`${name}: HTTP ${response.status}`);
  return response.json();
}

function setLink(id, href) {
  const link = $(id);
  link.href = href;
  link.hidden = false;
  return link;
}

function issueUrl(repo, query) {
  return `${repo}/issues?${new URLSearchParams({ q: query })}`;
}

function renderTask(task, repo) {
  const item = document.createElement('li');
  const id = document.createElement('span');
  id.className = 'task-id';
  id.textContent = task.id;
  const title = document.createElement('h3');
  title.textContent = task.title;
  const description = document.createElement('p');
  description.textContent = task.description;
  const acceptance = document.createElement('p');
  acceptance.textContent = `验收：${task.acceptance}`;
  item.append(id, title, description, acceptance);
  if (repo) {
    const link = document.createElement('a');
    link.className = 'task-link';
    link.href = issueUrl(repo, `is:issue in:title "${task.id}"`);
    link.textContent = '查看 Issue ↗';
    item.append(link);
  }
  return item;
}

copy.addEventListener('click', async () => {
  try {
    await navigator.clipboard.writeText(prompt.textContent);
    $('copy-status').textContent = '已复制，可以贴给 Agent。';
  } catch {
    const range = document.createRange();
    range.selectNodeContents(prompt);
    const selection = window.getSelection();
    selection.removeAllRanges();
    selection.addRange(range);
    $('copy-status').textContent = '无法访问剪贴板，已选中文字，请手动复制。';
  }
});

const [deployment, tasks] = await Promise.allSettled([readJson('deployment.json'), readJson('tasks.json')]);
const record = deployment.status === 'fulfilled' ? deployment.value : null;
const status = $('check-status');
if (record) {
  const { repo, sha, runId } = record;
  const blob = `${repo}/blob/${sha}`;
  prompt.textContent = `克隆 ${repo}。${prompt.textContent}`;
  setLink('repo', repo).textContent = '代码仓库 ↗';
  setLink('guide', `${blob}/AGENTS.md`);
  setLink('ready', issueUrl(repo, 'is:issue is:open label:ready no:assignee'));
  setLink('statement-source', `${blob}/Problem1/Statement.lean`);
  setLink('proof-source', `${blob}/Problem1/Starter.lean`);
  setLink('ci', `${repo}/actions/runs/${runId}`);
  setLink('attempts', `${blob}/attempts/README.md`);
  status.textContent = 'Lean 已验';
  status.className = 'tag checked';
} else {
  status.textContent = '预览 · 无 CI 记录';
}
copy.hidden = false;
if (tasks.status === 'fulfilled') {
  $('task-list').replaceChildren(...tasks.value.map((task) => renderTask(task, record?.repo)));
} else {
  $('task-note').textContent = '未能加载任务索引。请查看仓库中的 site/tasks.json。';
}
