# Issue #4：逐项加强路线的精确反例

关联：<https://github.com/EricTianC/problem1/issues/4>（P1-04）。
目标：区分原命题与三个更强断言；以下反例均不否定原命题。
状态：三类均为 **已机检证明的精确反例（无 `sorry`/额外公理）**。
证明文件：`Problem1/Counterexamples.lean`；声明均在 `Problem1` 命名空间。
记 `G₃(t) = 1 + t + t²`，非对角乘积遍历全部有序对 `i ≠ j`。

## 1. 朴素三角不等式逐项界

否定：对任意三阶复 Hermitian PSD 矩阵，把每个非对角因子换成
`1 + ‖aᵢⱼ‖` 或 `1 + √(aᵢᵢ aⱼⱼ)` 后，乘积仍不超过 `∏ᵢ G₃(aᵢᵢ)`。
这里对角元按实数理解；Lean 中取 `.re`。
矩阵：`allOnesMatrix 3`，即每个条目都为 `1` 的三阶矩阵。
PSD 理由：全一列向量 `v` 的 Gram 矩阵 `vvᴴ`。
六个非对角因子均为 `2`，故左边 `2⁶ = 64`；右边 `3³ = 27`。
精确矛盾：`64 > 27`，两种替换都失败。
已验证：`allOnesMatrix_posSemidef`、`not_termwise_abs_bound_three`、
`not_termwise_sqrt_bound_three`。
失败的是这些上界的乘积估计；各自的单项三角不等式仍成立。

## 2. 实数域 AM-GM 加强不能直接推广到复数域

否定：三阶复 PSD 且 `aᵢᵢ ≤ 1` 时，
`∏ᵢ≠ⱼ ‖1 - aᵢⱼ‖ ≤ ∏ᵢ (1 + aᵢᵢ/2)²`。
令 `ω = exp(2πi/3)`，`v = (1, ω, ω²)`，取 `A = vvᴴ/2`。
精确矩阵为 `[[1, ω², ω], [ω, 1, ω²], [ω², ω, 1]]/2`。
Lean 定义：`rootsOfUnityMatrix 3 (1/2)`；其 PSD 性由非负倍 Gram 矩阵得到。
全部对角元为 `1/2`，满足上界，且不等于 `1`。
任意维等号族给出全乘积等式；对角乘积为 `(1/2)³ > 0`。
提取对角项后，非对角乘积为 `(7/4)³ = 343/64 = 21952/4096`。
所提加强的右边为 `(5/4)⁶ = 15625/4096`，严格较小。
已验证：`rootsOfUnityMatrix_posSemidef`、`rootsOfUnityMatrix_diag`、
`rootsOfUnityMatrix_eq`、`not_real_amgm_strengthening_complex_three`。
等号族证明使用多项式 `Xⁿ - tⁿ` 的分解，直接在 `X = 1` 处取值。

## 3. 仅两两 2×2 约束不足

否定：仅凭实对称性、非负对角和 `aᵢⱼ² ≤ aᵢᵢaⱼⱼ` 即可推出非对角界。
矩阵：`pairwiseCounterexample = [[1,-1,-1],[-1,1,-1],[-1,-1,1]]`。
它对称、对角均为 `1`，每一条两两约束都取等号。
但对 `x = (1,1,1)`，有 `xᵀAx = -3 < 0`，因此不是全局 PSD。
非对角乘积为 `2⁶ = 64`，几何和乘积为 `3³ = 27`。
已验证：`pairwiseCounterexample_isHermitian`、`pairwiseCounterexample_diag_nonneg`、
`pairwiseCounterexample_two_by_two`、`pairwiseCounterexample_not_posSemidef`、
`pairwiseCounterexample_violates_offDiag`、`not_offDiag_from_two_by_two_only`。

## 可保留的路线与复现

反例要求保留全局 PSD 耦合，例如附录 B.1 的 `xᴴAx ≥ 0` 或 §2 的 Schur 幂。
实数域附录 A 的结论仍成立，见 `Problem1/RealSymmetric.lean`。
复现：`lake exe mk_all --lib Problem1 --check`、`lake build`。
再用 `lake env lean --stdin` 导入 `Problem1` 并对新增公开定理执行 `#print axioms`。
全部依赖均限于 `propext`、`Classical.choice`、`Quot.sound`。
