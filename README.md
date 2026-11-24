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
