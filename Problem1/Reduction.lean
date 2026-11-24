module

public import Problem1.Statement
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Diagonal factor extraction and inversion reduction for the seminar inequality.

All comparisons are real inequalities between complex norms. The complex order
is used only for positive semidefiniteness and its nonnegative diagonal entries.
-/

open scoped BigOperators ComplexOrder

namespace Problem1

noncomputable section

@[expose] public def geomSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ k

public theorem geomSum_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ geomSum n x := by
  exact Finset.sum_nonneg fun k _ => pow_nonneg hx k

public theorem geomSum_pos {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < geomSum n x := by
  exact Finset.sum_pos' (fun k _ => pow_nonneg hx k)
    ⟨0, Finset.mem_range.mpr hn, by simp⟩

public theorem one_sub_mul_geomSum (n : ℕ) (x : ℝ) :
    (1 - x) * geomSum n x = 1 - x ^ n := by
  induction n with
  | zero => simp [geomSum]
  | succ n ih =>
    simp only [geomSum, Finset.sum_range_succ] at *
    rw [pow_succ]
    nlinarith

public theorem abs_one_sub_mul_geomSum {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    |1 - x| * geomSum n x = |1 - x ^ n| := by
  rw [← one_sub_mul_geomSum, abs_mul, abs_of_nonneg (geomSum_nonneg hx)]

public theorem norm_one_sub_pow_eq {n : ℕ} {z : ℂ} (hz : 0 ≤ z) :
    ‖1 - z ^ n‖ = ‖1 - z‖ * geomSum n z.re := by
  have hr := (Complex.nonneg_iff.mp hz).1
  have he : z = (z.re : ℂ) := Complex.eq_re_of_ofReal_le hz
  conv_lhs => rw [he]
  conv_rhs => lhs; rw [he]
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using (abs_one_sub_mul_geomSum (n := n) hr).symm

public theorem posSemidef_diag_re_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : 0 ≤ (A i i).re :=
  (Complex.nonneg_iff.mp hA.diag_nonneg).1

public theorem posSemidef_diag_im_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : (A i i).im = 0 :=
  (Complex.nonneg_iff.mp hA.diag_nonneg).2.symm

public theorem posSemidef_diag_eq_ofReal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : A i i = ((A i i).re : ℂ) :=
  Complex.eq_re_of_ofReal_le hA.diag_nonneg

public theorem posSemidef_entry_conj {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i j : Fin n) : A j i = star (A i j) := by
  exact (hA.1.apply j i).symm

@[expose] public def OffDiagGoal (n : ℕ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
    (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ≤ ∏ i, geomSum n (A i i).re

public theorem goal_zero : Goal 0 := by
  intro A _
  simp

public theorem goal_of_exists_diag_eq_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (_hA : A.PosSemidef) (h1 : ∃ i, A i i = 1) :
    (∏ i, ∏ j, ‖1 - A i j‖) ≤ ∏ i, ‖1 - (A i i) ^ n‖ := by
  obtain ⟨i, hi⟩ := h1
  have hl : (∏ i, ∏ j, ‖1 - A i j‖) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
  have hr : (∏ i, ‖1 - (A i i) ^ n‖) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
  rw [hl, hr]

public theorem prod_diag_mul_offDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∏ i, ∏ j, ‖1 - A i j‖) =
      (∏ i, ‖1 - A i i‖) * ∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖ := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

public theorem goal_of_offDiag_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef)
    (hoff : (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ≤
      ∏ i, geomSum n (A i i).re) :
    (∏ i, ∏ j, ‖1 - A i j‖) ≤ ∏ i, ‖1 - (A i i) ^ n‖ := by
  simp_rw [norm_one_sub_pow_eq hA.diag_nonneg]
  rw [Finset.prod_mul_distrib, prod_diag_mul_offDiag]
  exact mul_le_mul_of_nonneg_left hoff (Finset.prod_nonneg fun _ _ => norm_nonneg _)

public theorem goal_iff_offDiag_of_diag_ne_one {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hne : ∀ i, A i i ≠ 1) :
    ((∏ i, ∏ j, ‖1 - A i j‖) ≤ ∏ i, ‖1 - (A i i) ^ n‖) ↔
      ((∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ≤
        ∏ i, geomSum n (A i i).re) := by
  simp_rw [norm_one_sub_pow_eq hA.diag_nonneg]
  rw [Finset.prod_mul_distrib, prod_diag_mul_offDiag]
  apply mul_le_mul_iff_right₀
  exact Finset.prod_pos fun i _ => norm_pos_iff.mpr (sub_ne_zero.mpr (hne i).symm)

public theorem goal_of_offDiagGoal {n : ℕ} (h : OffDiagGoal n) : Goal n := by
  intro A hA
  exact goal_of_offDiag_le hA (h A hA)

public theorem posSemidef_real_quad_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * (A i j).re := by
  have h := (Complex.nonneg_iff.mp
    (hA.dotProduct_mulVec_nonneg (fun i => (x i : ℂ)))).1
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, Complex.mul_re,
    mul_comm, mul_left_comm, mul_assoc] using h

public theorem posSemidef_norm_sq_le_diag_mul {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (i j : Fin n) :
    ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := by
  let t := (A i i).re
  let u := (A j j).re
  let v := ‖A i j‖ ^ 2
  have ht : 0 ≤ t := posSemidef_diag_re_nonneg hA i
  have hu : 0 ≤ u := posSemidef_diag_re_nonneg hA j
  have hv : 0 ≤ v := sq_nonneg _
  have hquad (a b : ℝ) : 0 ≤ t * a ^ 2 - 2 * a * b * v + u * b ^ 2 * v := by
    -- The two-coordinate submatrix also handles coinciding indices.
    have h := (Complex.nonneg_iff.mp ((hA.submatrix ![i, j]).dotProduct_mulVec_nonneg
      ![(a : ℂ), -(b : ℂ) * star (A i j)])).1
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.submatrix,
      posSemidef_entry_conj hA i j, Complex.mul_re, Complex.mul_im,
      posSemidef_diag_im_eq_zero hA] at h
    dsimp [t, u, v]
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [h]
  by_cases hu0 : u = 0
  · by_contra hn
    -- A zero diagonal forces the associated off-diagonal norm to vanish.
    have hvp : 0 < v := lt_of_le_of_lt (mul_nonneg ht hu) (lt_of_not_ge hn)
    have h := hquad 1 ((t + 1) / v)
    have he : (t + 1) / v * v = t + 1 := div_mul_cancel₀ _ hvp.ne'
    rw [hu0] at h
    nlinarith
  · have h := hquad u 1
    have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    change v ≤ t * u
    nlinarith

public theorem inversion_geomSum_eq {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (_ht : 0 ≤ t) :
    (max 1 t) ^ (n - 1) * geomSum n (t / (max 1 t) ^ 2) = geomSum n t := by
  by_cases h : t ≤ 1
  · simp [max_eq_left h]
  · have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (lt_of_not_ge h))
    rw [max_eq_right (le_of_not_ge h)]
    have he : t / t ^ 2 = t⁻¹ := by field_simp
    rw [he, geomSum, geomSum, Finset.mul_sum, ← Finset.sum_range_reflect (fun k => t ^ k) n]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n - 1 := by have := Finset.mem_range.mp hk; omega
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ ht0)]
    rw [← pow_add, Nat.sub_add_cancel hk']

public theorem complex_inversion_sq_ineq {a : ℂ} {q : ℝ} (hq : 1 ≤ q)
    (ha : ‖a‖ ^ 2 ≤ q) : ‖1 - a‖ ^ 2 ≤ q * ‖1 - a / (q : ℂ)‖ ^ 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have he : ‖1 - a / (q : ℂ)‖ ^ 2 * q ^ 2 =
      q ^ 2 - 2 * q * a.re + ‖a‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.div_ofReal_re, Complex.div_ofReal_im]
    field_simp
    ring
  have hf : ‖1 - a‖ ^ 2 = 1 - 2 * a.re + ‖a‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have hp := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr ha)
  nlinarith

public theorem complex_inversion_norm_ineq {a : ℂ} {q : ℝ} (hq : 1 ≤ q)
    (ha : ‖a‖ ^ 2 ≤ q) : ‖1 - a‖ ≤ Real.sqrt q * ‖1 - a / (q : ℂ)‖ := by
  have h := complex_inversion_sq_ineq hq ha
  have hs := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hp : 0 ≤ Real.sqrt q * ‖1 - a / (q : ℂ)‖ := by positivity
  nlinarith [sq_nonneg (‖1 - a‖ - Real.sqrt q * ‖1 - a / (q : ℂ)‖)]

@[expose] public def invScale {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  max 1 (A i i).re

@[expose] public def invMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => ((invScale A i : ℝ) : ℂ)⁻¹) * A *
    Matrix.diagonal (fun i => ((invScale A i : ℝ) : ℂ)⁻¹)

public theorem invMatrix_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    invMatrix A i j = A i j / ((invScale A i * invScale A j : ℝ) : ℂ) := by
  simp [invMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv,
    mul_comm, mul_assoc]

public theorem invMatrix_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) : (invMatrix A).PosSemidef := by
  simpa [invMatrix, star_inv, Pi.star_def] using hA.conjTranspose_mul_mul_same
    (Matrix.diagonal (fun i => ((invScale A i : ℝ) : ℂ)⁻¹))

public theorem invMatrix_diag_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (_hA : A.PosSemidef) (i : Fin n) :
    (invMatrix A i i).re = (A i i).re / (invScale A i) ^ 2 := by
  rw [invMatrix_apply, Complex.div_ofReal_re, pow_two]

public theorem invMatrix_diag_re_le_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) : (invMatrix A i i).re ≤ 1 := by
  rw [invMatrix_diag_re hA]
  have h1 : 1 ≤ invScale A i := le_max_left _ _
  have ht : (A i i).re ≤ invScale A i := le_max_right _ _
  apply (div_le_one (by positivity : 0 < (invScale A i) ^ 2)).mpr
  nlinarith

public theorem prod_offDiag_swap {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, f i j) =
      ∏ j, ∏ i ∈ Finset.univ.erase j, f i j := by
  simp only [← Finset.filter_ne', Finset.prod_filter]
  rw [Finset.prod_comm]
  simp only [ne_comm]

public theorem prod_offDiag_mul {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j) = ∏ i, (x i ^ 2) ^ (n - 1) := by
  simp_rw [Finset.prod_mul_distrib]
  rw [prod_offDiag_swap (fun _ j => x j)]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

public theorem offDiag_le_of_invMatrix {n : ℕ} (hn : 1 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hB : (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - invMatrix A i j‖) ≤
      ∏ i, geomSum n (invMatrix A i i).re) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ≤
      ∏ i, geomSum n (A i i).re := by
  have hd (i : Fin n) : 1 ≤ invScale A i := le_max_left _ _
  have hd0 (i : Fin n) : 0 ≤ invScale A i := le_trans zero_le_one (hd i)
  have he (i j : Fin n) : ‖1 - A i j‖ ≤
      (Real.sqrt (invScale A i) * Real.sqrt (invScale A j)) * ‖1 - invMatrix A i j‖ := by
    rw [invMatrix_apply, ← Real.sqrt_mul (hd0 i)]
    apply complex_inversion_norm_ineq
    · nlinarith [hd i, hd j, mul_nonneg (sub_nonneg.mpr (hd i)) (sub_nonneg.mpr (hd j))]
    · exact (posSemidef_norm_sq_le_diag_mul hA i j).trans
        (mul_le_mul (le_max_right _ _) (le_max_right _ _)
          (posSemidef_diag_re_nonneg hA j) (hd0 i))
  calc
    _ ≤ ∏ i, ∏ j ∈ Finset.univ.erase i,
        (Real.sqrt (invScale A i) * Real.sqrt (invScale A j)) * ‖1 - invMatrix A i j‖ := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Finset.prod_nonneg fun j _ => norm_nonneg _
      · intro i _; exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => he i j)
    _ = (∏ i, (invScale A i) ^ (n - 1)) *
        (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - invMatrix A i j‖) := by
      simp_rw [Finset.prod_mul_distrib]
      rw [prod_offDiag_swap (fun _ j => Real.sqrt (invScale A j))]
      simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← mul_pow, ← pow_two, Real.sq_sqrt (hd0 i)]
    _ ≤ (∏ i, (invScale A i) ^ (n - 1)) * ∏ i, geomSum n (invMatrix A i i).re :=
      mul_le_mul_of_nonneg_left hB (Finset.prod_nonneg fun i _ => pow_nonneg (hd0 i) _)
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [invMatrix_diag_re hA]
      exact inversion_geomSum_eq hn (posSemidef_diag_re_nonneg hA i)

public theorem goal_of_unit_diag_offDiag {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ (B : Matrix (Fin n) (Fin n) ℂ), B.PosSemidef →
      (∀ i, (B i i).re ≤ 1) →
      (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - B i j‖) ≤ ∏ i, geomSum n (B i i).re) :
    Goal n := by
  intro A hA
  exact goal_of_offDiag_le hA (offDiag_le_of_invMatrix hn hA
    (h _ (invMatrix_posSemidef hA) (invMatrix_diag_re_le_one hA)))

end

end Problem1
