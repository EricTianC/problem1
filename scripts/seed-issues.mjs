import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';

const tasks = JSON.parse(readFileSync(new URL('../site/tasks.json', import.meta.url), 'utf8'));
const [repo, ...rest] = process.argv.slice(2);
if (!repo || rest.length || !/^[\w.-]+\/[\w.-]+$/.test(repo)) {
  console.error('用法：node scripts/seed-issues.mjs OWNER/REPO');
  process.exit(2);
}

const token = process.env.GH_TOKEN?.trim() || process.env.GITHUB_TOKEN?.trim()
  || spawnSync('gh', ['auth', 'token'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).stdout?.trim();
if (!token) {
  console.error('未找到 GitHub 凭据：请在本机设置 GH_TOKEN，或运行 gh auth login --web。');
  process.exit(2);
}

async function api(path, { body, allowMissing = false } = {}) {
  const method = body ? 'POST' : 'GET';
  const response = await fetch(`https://api.github.com/repos/${repo}${path}`, {
    method,
    headers: {
      Accept: 'application/vnd.github+json',
      Authorization: `Bearer ${token}`,
      'Content-Type': 'application/json',
      'X-GitHub-Api-Version': '2026-03-10',
    },
    body: body && JSON.stringify(body),
    redirect: 'error',
  });
  if (allowMissing && response.status === 404) return null;
  if (!response.ok) throw new Error(`GitHub ${method} ${path}: HTTP ${response.status}`);
  return response.json();
}

try {
  const existing = new Set();
  for (let page = 1; ; page++) {
    const issues = await api(`/issues?state=all&per_page=100&page=${page}`);
    for (const issue of issues) {
      if (!('pull_request' in issue)) existing.add(issue.title.split(' ', 1)[0]);
    }
    if (issues.length < 100) break;
  }
  if (!await api('/labels/ready', { allowMissing: true })) {
    await api('/labels', { body: { name: 'ready', color: '0e8a16', description: '可认领' } });
  }
  for (const { id, title, description, acceptance } of tasks) {
    if (existing.has(`[${id}]`)) continue;
    const issue = await api('/issues', { body: {
      title: `[${id}] ${title}`,
      body: `## 目标\n\n${description}\n\n## 验收\n\n${acceptance}\n\n认领请留言；贡献流程见仓库的 AGENTS.md。`,
      labels: ['ready'],
    } });
    console.log(issue.html_url);
  }
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
