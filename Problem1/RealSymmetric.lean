module

public import Problem1.Reduction
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Appendix A: the real PSD inequality in every dimension.

The weighted quadratic form controls the sum of all ordered off-diagonal
factors. AM-GM then gives the unit-diagonal estimate. Diagonal congruence and
the scalar inversion inequality remove the unit bound without dividing by
any factor `1 - A i i`.
-/

open scoped BigOperators ComplexOrder

namespace Problem1

public theorem real_posSemidef_quad_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * A i j := by
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc] using hA.dotProduct_mulVec_nonneg x

public theorem real_posSemidef_sq_le_diag_mul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i j : Fin n) : (A i j) ^ 2 ≤ A i i * A j j := by
  have hc : A j i = A i j := by simpa using (hA.1.apply j i).symm
  have hq (a b : ℝ) : 0 ≤ A i i * a ^ 2 + 2 * a * b * A i j + A j j * b ^ 2 := by
    have h := (hA.submatrix ![i, j]).dotProduct_mulVec_nonneg ![a, b]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.submatrix, hc] at h
    nlinarith [h]
  have hi : 0 ≤ A i i := hA.diag_nonneg
  have hj : 0 ≤ A j j := hA.diag_nonneg
  by_cases hz : A j j = 0
  · have h := hq 1 (-(A i i + 1) / (2 * A i j))
    by_cases he : A i j = 0
    · simp [he, hz]
    · have he' : 2 * A i j ≠ 0 := mul_ne_zero (by norm_num) he
      have hd := div_mul_cancel₀ (-(A i i + 1)) he'
      rw [hz] at h
      nlinarith
  · have h := hq (A j j) (-A i j)
    have hp : 0 < A j j := lt_of_le_of_ne hj (Ne.symm hz)
    nlinarith

public theorem one_add_div_pow_le_geomSum {m : ℕ} (hm : 1 ≤ m) {t : ℝ}
    (ht : 0 ≤ t) : (1 + t / (m : ℝ)) ^ m ≤ geomSum (m + 1) t := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [add_comm, add_pow, geomSum]
  apply Finset.sum_le_sum
  intro k _
  simp only [one_pow, mul_one]
  calc
    _ ≤ (t / (m : ℝ)) ^ k * (m : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.choose_le_pow m k)
        (pow_nonneg (div_nonneg ht (Nat.cast_nonneg m)) k)
    _ = t ^ k := by rw [← mul_pow, div_mul_cancel₀ _ hm0]

private theorem weighted_real_sum_le {n : ℕ} (hn : 1 ≤ n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) (x : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j * (1 - B i j)) ≤
      ∑ i, x i ^ 2 * (((n - 1 : ℕ) : ℝ) + B i i) := by
  let f := fun i j => x i * x j * (1 - B i j)
  have hs : (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) + (∑ i, f i i) =
      ∑ i, ∑ j, f i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hall : (∑ i, ∑ j, f i j) = (∑ i, x i) ^ 2 -
      (∑ i, ∑ j, x i * x j * B i j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    ring
  have he : (∑ i, x i ^ 2 * (((n - 1 : ℕ) : ℝ) + B i i)) =
      (n : ℝ) * (∑ i, x i ^ 2) - ∑ i, f i i := by
    rw [Nat.cast_sub hn]
    simp only [Nat.cast_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    ring
  have hq := real_posSemidef_quad_nonneg hB x
  have hcs : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, x i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
  rw [hall] at hs
  rw [he]
  change (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) ≤ _
  linarith

private theorem real_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hc : 0 < s.card) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hs : ∑ i ∈ s, f i ≤ (s.card : ℝ)) : ∏ i ∈ s, f i ≤ 1 := by
  have hc' : 0 < (s.card : ℝ) := by exact_mod_cast hc
  have ham := Real.geom_mean_le_arith_mean s (fun _ => 1) f
    (fun _ _ => zero_le_one) (by simpa using hc') hf
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at ham
  have hroot : (∏ i ∈ s, f i) ^ (s.card : ℝ)⁻¹ ≤ 1 :=
    ham.trans ((div_le_one hc').mpr hs)
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (Finset.prod_nonneg hf) _) hroot hc'.le
  rw [← Real.rpow_mul (Finset.prod_nonneg hf), inv_mul_cancel₀ hc'.ne',
    Real.rpow_one, Real.one_rpow] at hp
  exact hp

private theorem real_unit_entry_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) (hdiag : ∀ i, B i i ≤ 1) (i j : Fin n) : B i j ≤ 1 := by
  have h := real_posSemidef_sq_le_diag_mul hB i j
  have hp : B i i * B j j ≤ 1 := by
    simpa using mul_le_mul (hdiag i) (hdiag j) hB.diag_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [sq_nonneg (B i j - 1)]

public theorem real_posSemidef_unit_offDiag_le {n : ℕ} (hn : 2 ≤ n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) (hdiag : ∀ i, B i i ≤ 1) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - B i j)) ≤ ∏ i, geomSum n (B i i) := by
  let m : ℝ := ((n - 1 : ℕ) : ℝ)
  let c := fun i => 1 + B i i / m
  let x := fun i => (Real.sqrt (c i))⁻¹
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < n - 1 by omega)
  have hc (i) : 0 < c i := by
    have hi : 0 ≤ B i i := hB.diag_nonneg
    dsimp [c]
    positivity
  have hx (i) : 0 ≤ x i := by dsimp [x]; positivity
  have hb (i j) : 0 ≤ 1 - B i j := sub_nonneg.mpr (real_unit_entry_le hB hdiag i j)
  have hxc (i) : x i ^ 2 * c i = 1 := by
    dsimp [x]
    rw [inv_pow, Real.sq_sqrt (hc i).le, inv_mul_cancel₀ (hc i).ne']
  have hsum : (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j * (1 - B i j)) ≤
      (n : ℝ) * m := by
    calc
      _ ≤ ∑ i, x i ^ 2 * (m + B i i) := weighted_real_sum_le (by omega) hB x
      _ = ∑ _i : Fin n, m := by
        apply Finset.sum_congr rfl
        intro i _
        have he : m + B i i = m * c i := by dsimp [c]; field_simp
        rw [he, mul_left_comm, hxc, mul_one]
      _ = _ := by simp
  let s := (Finset.univ : Finset (Fin n)).sigma (fun i => Finset.univ.erase i)
  let f := fun p : (i : Fin n) × Fin n => x p.1 * x p.2 * (1 - B p.1 p.2)
  have hcard : s.card = n * (n - 1) := by simp [s, Finset.card_sigma]
  have hp : (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j * (1 - B i j)) ≤ 1 := by
    have hp := real_prod_le_one s f
      (by rw [hcard]; exact Nat.mul_pos (by omega) (by omega))
      (fun p _ => mul_nonneg (mul_nonneg (hx _) (hx _)) (hb _ _))
      (by simpa [s, f, Finset.sum_sigma, hcard, Nat.cast_mul, m] using hsum)
    simpa [s, f, Finset.prod_sigma] using hp
  have hfactor : (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j * (1 - B i j)) =
      (∏ i, (x i ^ 2) ^ (n - 1)) * (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - B i j)) := by
    calc
      _ = (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j) *
          (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - B i j)) := by
        simp only [Finset.prod_mul_distrib]
      _ = _ := by rw [prod_offDiag_mul]
  rw [hfactor] at hp
  have hcancel : (∏ i, c i ^ (n - 1)) * (∏ i, (x i ^ 2) ^ (n - 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [← mul_pow, mul_comm (c _) (x _ ^ 2), hxc, one_pow, Finset.prod_const_one]
  have hmul := mul_le_mul_of_nonneg_left hp
    (Finset.prod_nonneg (s := Finset.univ) (fun i _ => pow_nonneg (hc i).le (n - 1)))
  rw [← mul_assoc, hcancel, one_mul, mul_one] at hmul
  apply hmul.trans
  apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hc i).le _)
  intro i _
  simpa [c, m, Nat.sub_add_cancel (show 1 ≤ n by omega)] using
    one_add_div_pow_le_geomSum (m := n - 1) (by omega) (hB.diag_nonneg (i := i))

public theorem real_posSemidef_offDiag_le {n : ℕ} (hn : 1 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, |1 - A i j|) ≤ ∏ i, geomSum n (A i i) := by
  by_cases hn1 : n = 1
  · subst n
    simp [geomSum]
  have hn2 : 2 ≤ n := by omega
  let d := fun i => max 1 (A i i)
  let D := Matrix.diagonal (fun i => (d i)⁻¹)
  let B := D * A * D
  have hd (i) : 1 ≤ d i := le_max_left _ _
  have hd0 (i) : 0 ≤ d i := le_trans zero_le_one (hd i)
  have hb (i j) : B i j = A i j / (d i * d j) := by
    simp [B, D, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  have hB : B.PosSemidef := by
    simpa [B, D] using hA.conjTranspose_mul_mul_same D
  have hdiag (i) : B i i ≤ 1 := by
    rw [hb]
    apply (div_le_one (mul_pos (lt_of_lt_of_le zero_lt_one (hd i))
      (lt_of_lt_of_le zero_lt_one (hd i)))).mpr
    have ht : A i i ≤ d i := le_max_right _ _
    nlinarith [hd i]
  have he (i j) : |1 - A i j| ≤
      (Real.sqrt (d i) * Real.sqrt (d j)) * (1 - B i j) := by
    -- Reuse the scalar complex inversion lemma on the real embedding.
    have hq : 1 ≤ d i * d j := by
      nlinarith [hd i, hd j, mul_nonneg (sub_nonneg.mpr (hd i)) (sub_nonneg.mpr (hd j))]
    have ha : (A i j) ^ 2 ≤ d i * d j :=
      (real_posSemidef_sq_le_diag_mul hA i j).trans
        (mul_le_mul (le_max_right _ _) (le_max_right _ _) hA.diag_nonneg (hd0 i))
    have h := complex_inversion_norm_ineq (a := (A i j : ℂ)) hq
      (by simpa using ha)
    rw [← Real.sqrt_mul (hd0 i), hb]
    have hnonneg : 0 ≤ 1 - A i j / (d i * d j) := by
      rw [← hb]
      exact sub_nonneg.mpr (real_unit_entry_le hB hdiag i j)
    simpa only [← Complex.ofReal_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] using h
  calc
    _ ≤ ∏ i, ∏ j ∈ Finset.univ.erase i,
        (Real.sqrt (d i) * Real.sqrt (d j)) * (1 - B i j) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Finset.prod_nonneg fun j _ => abs_nonneg _
      · intro i _; exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => he i j)
    _ = (∏ i, (d i) ^ (n - 1)) *
        (∏ i, ∏ j ∈ Finset.univ.erase i, (1 - B i j)) := by
      simp_rw [Finset.prod_mul_distrib]
      rw [prod_offDiag_swap (fun _ j => Real.sqrt (d j))]
      simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← mul_pow, ← pow_two, Real.sq_sqrt (hd0 i)]
    _ ≤ (∏ i, (d i) ^ (n - 1)) * ∏ i, geomSum n (B i i) :=
      mul_le_mul_of_nonneg_left (real_posSemidef_unit_offDiag_le hn2 hB hdiag)
        (Finset.prod_nonneg fun i _ => pow_nonneg (hd0 i) _)
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [hb, ← pow_two]
      exact inversion_geomSum_eq hn hA.diag_nonneg

public theorem real_posSemidef_goal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) :
    (∏ i, ∏ j, |1 - A i j|) ≤ ∏ i, |1 - (A i i) ^ n| := by
  by_cases hn : n = 0
  · subst n; simp
  have hoff := real_posSemidef_offDiag_le (by omega : 1 ≤ n) hA
  have he : (∏ i, ∏ j, |1 - A i j|) =
      (∏ i, |1 - A i i|) * (∏ i, ∏ j ∈ Finset.univ.erase i, |1 - A i j|) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ =>
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [he]
  calc
    _ ≤ (∏ i, |1 - A i i|) * ∏ i, geomSum n (A i i) :=
      mul_le_mul_of_nonneg_left hoff (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => abs_one_sub_mul_geomSum hA.diag_nonneg

public theorem complex_of_real_entries_goal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hreal : ∀ i j, (A i j).im = 0) :
    (∏ i, ∏ j, ‖1 - A i j‖) ≤ ∏ i, ‖1 - (A i i) ^ n‖ := by
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j).re
  have he (i j) : A i j = (B i j : ℂ) := by
    apply Complex.ext <;> simp [B, hreal]
  have hB : B.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      have h := congrArg Complex.re (posSemidef_entry_conj hA i j)
      change (B j i) = B i j
      exact h
    · intro x
      simpa [B, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm,
        mul_assoc] using posSemidef_real_quad_nonneg hA x
  simp_rw [he]
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using real_posSemidef_goal B hB

end Problem1
