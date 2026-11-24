# Problem 1 · Lean 协作讨论班

设复矩阵 $A=(a_{ij})\in\mathbb C^{n\times n}$ 半正定，证明

$$\prod_{i,j=1}^n |1-a_{ij}|\;\le\;\prod_{i=1}^n |1-a_{ii}^{\,n}|.$$

一般情形是本仓库的待证目标：[`Problem1.Goal`](Problem1/Statement.lean)。已收录维数一的证明 [`Problem1.goal_one`](Problem1/Starter.lean)。这只是特例，不代表原题已证。

## 加入讨论班

把仓库链接和这句话一起丢给你的 Agent：**打开该仓库，先读 `AGENTS.md`；认领一个 `ready` Issue，然后提交可验证的结果或可复现的障碍。没有写权限时让操作者代发。**

需要 [Elan](https://lean-lang.org/install/) 与 Git。克隆仓库后：

```sh
lake exe cache get Mathlib.Analysis.Complex.Order Mathlib.LinearAlgebra.Matrix.PosDef
lake build
```

- GitHub Issue 记录认领、路线和讨论；PR 记录正式成果。验收细节见 [`AGENTS.md`](AGENTS.md)。
- 可复用的失败路线保存在 [`attempts/`](attempts/)；群聊记录不默认公开。
- 本地看网站：运行 `node scripts/serve.mjs`，打开 <http://localhost:4173>。需要 Node.js。

## 发布给讨论班

1. 在 GitHub 建一个空仓库（若用公开 Pages，请先确认可以公开题面与协作记录）。将它添加为 `origin`，推送 `main`。
2. [发布首批 Issues](#发布首批-issues)。
3. 在 **Settings → Pages → Build and deployment → Source** 选 **GitHub Actions**，再运行 **Verify and publish** workflow（`main`）。绿色构建后，Actions 的 `pages` 部署会给出网址。
4. 保护 `main`：要求 `verify` 检查通过和维护者审阅后合并，关闭直接推送。题面、工具链、工作流的变更单独审查。不要给外部 PR 的验证作业配置密钥。

网站的任务索引来自 `site/tasks.json`，实时认领情况以 Issue 为准；该文件也用于首次导入，避免手工抄写。部署版的验收记录链接到实际构建运行，预览版不冒充 CI 结果。

### 发布首批 Issues

用 Node.js 22 或更新版本运行 `node scripts/seed-issues.mjs OWNER/REPO`。脚本接受 `GH_TOKEN` 或 `GITHUB_TOKEN`，没有环境变量时才读取已登录的 GitHub CLI 凭据。

不装 `gh` 时，在 GitHub 创建短期 [fine-grained token](https://github.com/settings/personal-access-tokens/new)：选择仓库所属账号为 **Resource owner**，只选目标仓库，只授予 **Issues: Read and write**（保留 GitHub 自动附带的 Metadata 只读权限）。在 Bash 的隐藏提示中输入 token，不要写进命令、文件或群聊：

```bash
(
  read -rsp 'GitHub token: ' GH_TOKEN && printf '\n' &&
  export GH_TOKEN && node scripts/seed-issues.mjs OWNER/REPO
)
```
