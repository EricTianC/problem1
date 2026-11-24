# Problem 1 · Lean 协作讨论班

**当前是讨论班试跑阶段。** 专用 Lean 验证主机就绪前不发布网站；先用 GitHub Issues / PR 同步思路、代码和卡点，不要求把探索结果全部合入 `main`。

设复矩阵 $A=(a_{ij})\in\mathbb C^{n\times n}$ 半正定，证明

$$\prod_{i,j=1}^n |1-a_{ij}|\;\le\;\prod_{i=1}^n |1-a_{ii}^{\,n}|.$$

一般情形是本仓库的待证目标：[`Problem1.Goal`](Problem1/Statement.lean)。已收录维数一的证明 [`Problem1.goal_one`](Problem1/Starter.lean)。这只是特例，不代表原题已证。

## 加入讨论班

把 [Lean 4 形式化参考提示词](PROMPT.md) 复制给你的 Agent，再附上一个 [Issue](https://github.com/EricTianC/problem1/issues)、一条引理或一段纸笔推导。不用等到有完整证明再分享。

需要 [Elan](https://lean-lang.org/install/) 与 Git。克隆仓库后：

```sh
lake exe cache get Mathlib.Analysis.Complex.Order Mathlib.LinearAlgebra.Matrix.PosDef
lake build
```

- 有思路、反例线索或卡点：在相关 Issue 简短回复「目标 / 进展 / 验证 / 下一步」；没有现成 Issue 再新开。
- 有值得共享的 Lean 代码：开 draft PR 并链接相关 Issue，不必立即请求审阅或合并。具体约定见 [`AGENTS.md`](AGENTS.md)。
- 可复用的失败路线保存在 [`attempts/`](attempts/)；群聊记录不默认公开。
- 本地看网站：运行 `node scripts/serve.mjs`，打开 <http://localhost:4173>。需要 Node.js。

## 维护者：验证与上线

试跑不要求批量建任务：[手动开 Issue](https://github.com/EricTianC/problem1/issues/new) 即可；需要时才[导入首批 Issues](#发布首批-issues)。正式合并到 `main` 仍走 PR 审阅和 `verify`；当前的 GitHub Actions 不是专用验证主机。

准备公开网站时，先把专用验证主机接入并验证其结果，再到 **Settings → Pages → Build and deployment → Source** 选 **GitHub Actions**。之后在 **Settings → Secrets and variables → Actions → Variables** 将仓库变量 `PUBLISH_PAGES` 设为 `true`，在 `main` 上运行 **Verify and publish**。[Pages 网址](https://erictianc.github.io/problem1/)以 `pages` 作业成功部署为准。

网站的任务索引来自 `site/tasks.json`，实时认领情况以 Issue 为准；该文件也用于首次导入，避免手工抄写。部署版的验收记录链接到实际构建运行，预览版不冒充 CI 结果。

Pages 在 `verify` 通过后由 `package-pages` 上传产物，再由 `pages` 部署。若只有 `pages` 失败且该次运行的 `github-pages` 产物仍在，可点 **Re-run failed jobs** 重试部署；产物已过期则在 `main` 上发起一次新的 **Run workflow**。

### 发布首批 Issues

**批量发布需要仓库写权限，不需要 Owner、Admin 或 Maintain。** 普通成员可以在可访问的仓库里认领、评论和提任务；但 [GitHub 创建 Issue 的 API](https://docs.github.com/en/rest/issues/issues#create-an-issue) 只允许有推送权限的用户在创建时设置标签，权限不足会静默丢弃 `ready`。组织仓库的 `Triage` 足够给现有 Issue 贴标签和派单，不足以运行本批量发布流程。

#### 给协作者授权

1. 当前 `EricTianC/problem1` 是个人仓库。仓库所有者在 **Settings → Access → Collaborators → Add people** 邀请对方的 GitHub 账号。对方接受邀请后即有仓库写权限。若迁到 Organization，给负责发布的人该仓库的 `Write` 权限即可。
2. 只邀请实际负责发布的人，保留 `main` 的合并保护。每人用自己的 GitHub 账号授权，不共用仓库所有者的 token。

#### 用自己的账号发布

需要 Node.js 22 或更新版本。**受邀协作者优先用 GitHub CLI 登录**，在浏览器里用自己的账号完成授权：

```bash
gh auth login --hostname github.com --web
node scripts/seed-issues.mjs EricTianC/problem1
```

不装 `gh` 时，脚本接受 `GH_TOKEN` 或 `GITHUB_TOKEN`（两者都未设置才读取 `gh` 登录凭据）。根据身份选短期 token：

- **仓库所有者，或有该仓库 `Write` 权限的组织成员：**用 [fine-grained token](https://github.com/settings/personal-access-tokens/new)，选实际仓库归属为 **Resource owner**，只选目标仓库，授予 **Issues: Read and write**，保留自动附带的 Metadata 只读权限。组织要求审批时，须先获批准。
- **受邀的个人仓库协作者，或组织的外部协作者：**[GitHub 不支持用 fine-grained token 以这些身份写入仓库](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens#fine-grained-personal-access-tokens-limitations)。不用 `gh` 时可用自己的短期 [classic token](https://github.com/settings/tokens/new)：公开仓库选 `public_repo`，私有仓库需要 `repo`，并遵守组织的令牌策略。Classic token 无法绑定到单一仓库，权限范围更广；也可以请仓库所有者代发。

在 Bash 的隐藏提示中输入 token，不要发给 Agent、贴进群聊或写进文件：

```bash
(
  read -rsp 'GitHub token: ' GH_TOKEN && printf '\n' &&
  export GH_TOKEN && node scripts/seed-issues.mjs EricTianC/problem1
)
```

发布后在 GitHub 的 Issues 页用 `is:issue is:open label:ready` 确认新任务已带标签。脚本按任务编号跳过已存在的 Issue；不会覆写现有认领状态。
