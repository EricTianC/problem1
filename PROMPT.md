# Lean 4 形式化参考提示词

把下面整段发给能运行 Git 和 Lean 的 Agent，再附上一个 Issue 链接、一条自然语言引理，或一段需要检查的纸笔推导。一次只做一个明确的小目标；也欢迎只报告进展，不用急着合并。

```text
你在协作仓库 https://github.com/EricTianC/problem1 中帮助讨论班做 Lean 4 形式化。
先读 AGENTS.md 和 Problem1/Statement.lean。使用仓库固定的 Lean 与 Mathlib 版本，不修改工具链、依赖或 CI。

1. 读我给的 Issue、引理或纸笔推导。先用中文重述你要证明的命题和假设，列出最不确定的一步。逐项对照量词、类型、边界和原题，不要为了通过检查而添加假设或改 Problem1.Goal。如果只证明特例或更弱版本，明确写出来。
2. 先找 Mathlib 现成接口，优先查看相关模块和使用 #check。把推导拆成少量可单独验证的引理。若缺关键不等式，就先检查这一条；可以尝试低维反例，但数值近似只能作线索。对这题留意复数模与实数不等式的区别，和左边乘积包含所有有序对（包括对角项）。
3. 在自己的分支或不被 Problem1.lean 导入的 Scratch.lean 中试做。首次可运行 `lake exe cache get Mathlib.Analysis.Complex.Order Mathlib.LinearAlgebra.Matrix.PosDef`；若导入本仓库模块，先 `lake build`。用 `lake env lean Scratch.lean` 检查单文件。对要报告为已经证明的声明，运行 `#print axioms 声明名`，确认没有 sorryAx 或额外公理。新增正式模块时，再运行 `lake build`。不把有缺口、没运行或只测试样例的结论写成已证；不以自设公理或更换命题绕过检查。
4. 用中文交接四项：目标和 Lean 声明（或可复制的片段）；目前结论（本地验证通过／部分验证／仅思路）；实际命令与结果；最小的下一步或卡点。可附文件路径、分支或提交 SHA。若只得到纸笔思路或反例线索，也可以交接，不必凑证明。
5. 默认先把简报交给我预览，不擅自发帖或合并。已有 Issue 就建议回帖；有值得共享的代码才建议开 draft PR 并链接 Issue。不要索要 token；未实际发布时不要说已发布。
```
