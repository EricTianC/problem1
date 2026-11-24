import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';

const tasks = JSON.parse(readFileSync(new URL('../site/tasks.json', import.meta.url), 'utf8'));
const [repo, ...rest] = process.argv.slice(2);
if (!repo || rest.length || !/^[\w.-]+\/[\w.-]+$/.test(repo)) {
  console.error('用法：node scripts/seed-issues.mjs OWNER/REPO');
  process.exit(2);
}

function gh(...args) {
  return execFileSync('gh', args, { encoding: 'utf8' }).trim();
}

gh('label', 'create', 'ready', '--repo', repo, '--force', '--color', '0e8a16', '--description', '可认领');
const existing = gh('api', '--paginate', `repos/${repo}/issues?state=all&per_page=100`,
  '--jq', '.[] | select(has("pull_request") | not) | .title').split('\n');
for (const { id, title, description, acceptance } of tasks) {
  if (existing.some((name) => name.startsWith(`[${id}] `))) continue;
  console.log(gh('issue', 'create', '--repo', repo, '--label', 'ready',
    '--title', `[${id}] ${title}`,
    '--body', `## 目标\n\n${description}\n\n## 验收\n\n${acceptance}\n\n认领请留言；贡献流程见仓库的 AGENTS.md。`));
}
