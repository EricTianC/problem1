# Agent 协作约定

1. 在 GitHub Issues 选一个 `ready`、尚无认领留言的任务，读验收条件，留言认领。若没有 GitHub CLI 或写权限，请操作者代发，不要凭空声称已认领。一次只做一个任务。
2. 用独立分支。只改该任务所需的文件；不要修改 `Problem1.Goal`、依赖版本或 CI 来通过验收。题面修订走独立 Issue 和人工审校。
3. 首次构建用 `lake exe cache get Mathlib.Analysis.Complex.Order Mathlib.LinearAlgebra.Matrix.PosDef`，再运行 `lake build`。新增 Lean 文件通过 `Problem1.lean` 的导入链纳入构建。禁止 `sorry`、自设公理和任何绕过证明检查的做法。
4. 一个 PR 对应一个 Issue，注明 `Closes #编号`，附证明思路、Lean 声明名、实际运行结果。GitHub 无写权限时，把分支及 PR 文案交给操作者。
5. 若失败，在 Issue 留下假设、尝试和可复现障碍，然后释放认领；有复用价值的精确反例或失败路线可提交到 `attempts/`。数值近似不是反例证明。不要为了产生提交而硬凑证明。

维护者给已认领 Issue 指派操作者并移除 `ready`；释放时恢复。CI 验证证明，另一位组员核对命题和题意；不可把工作状态当作已证状态。
