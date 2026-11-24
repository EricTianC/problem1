module

public import Problem1.Reduction
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Low-dimensional cases and the general complex AM-GM off-diagonal estimate.

The AM-GM argument uses all ordered off-diagonal pairs, represented by a finite
sigma set so that its sum, product, and cardinality reduce to fiberwise operations.
-/

open scoped BigOperators ComplexOrder

namespace Problem1

public theorem scalar_two_ineq {t₁ t₂ : ℝ} {z : ℂ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hz : ‖z‖ ^ 2 ≤ t₁ * t₂) :
    ‖1 - z‖ ^ 2 ≤ (1 + t₁) * (1 + t₂) := by
  have hnorm : ‖1 - z‖ ≤ 1 + ‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  have ham : 2 * ‖z‖ ≤ t₁ + t₂ := by
    nlinarith [sq_nonneg (t₁ - t₂), norm_nonneg z]
  nlinarith [sq_nonneg (1 + ‖z‖ - ‖1 - z‖), norm_nonneg (1 - z)]

public theorem goal_two : Goal 2 := by
  intro A hA
  apply goal_of_offDiag_le hA
  have h := scalar_two_ineq (posSemidef_diag_re_nonneg hA 0)
    (posSemidef_diag_re_nonneg hA 1) (posSemidef_norm_sq_le_diag_mul hA 0 1)
  have hc : ‖1 - A 1 0‖ = ‖1 - A 0 1‖ := by
    rw [posSemidef_entry_conj hA 0 1, ← star_one, ← star_sub, norm_star]
    simp
  norm_num [Fin.prod_univ_two, Fin.univ_succ, geomSum, Finset.sum_range_succ]
  rw [show ({0, 1} : Finset (Fin 2)).erase 1 = {0} by decide]
  simpa [hc, pow_two] using h

private theorem norm_one_sub_sq (z : ℂ) :
    ‖1 - z‖ ^ 2 = 1 - 2 * z.re + ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

private theorem sum_offDiag_add_diag {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) + (∑ i, f i i) = ∑ i, ∑ j, f i j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- The weighted quadratic estimate underlying the complex AM-GM bound. -/
private theorem weighted_offDiag_sum_le {n : ℕ} (hn : 1 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j * ‖1 - A i j‖ ^ 2) ≤
      ∑ i, x i ^ 2 * (((n - 1 : ℕ) : ℝ) * (1 + (A i i).re ^ 2) + 2 * (A i i).re) := by
  let t := fun i => (A i i).re
  let g := fun i j => x i * x j * (1 - 2 * (A i j).re + t i * t j)
  have hg : (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j * ‖1 - A i j‖ ^ 2) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, g i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    dsimp [g, t]
    rw [norm_one_sub_sq]
    exact mul_le_mul_of_nonneg_left
      (add_le_add_right (posSemidef_norm_sq_le_diag_mul hA i j) _)
      (mul_nonneg (hx i) (hx j))
  have hdiag : (∑ i, g i i) = ∑ i, x i ^ 2 * (1 - t i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [g, t]
    ring
  have hall : (∑ i, ∑ j, g i j) =
      (∑ i, x i) ^ 2 - 2 * (∑ i, ∑ j, x i * x j * (A i j).re) +
        (∑ i, x i * t i) ^ 2 := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g]
    ring
  have hq := posSemidef_real_quad_nonneg hA x
  have hcx : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, x i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
  have hct : (∑ i, x i * t i) ^ 2 ≤ (n : ℝ) * ∑ i, (x i * t i) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => x i * t i))
  have hsplit := sum_offDiag_add_diag g
  rw [hdiag, hall] at hsplit
  have halg : (∑ i, x i ^ 2 * (((n - 1 : ℕ) : ℝ) * (1 + t i ^ 2) + 2 * t i)) =
      (n : ℝ) * (∑ i, x i ^ 2) + (n : ℝ) * (∑ i, (x i * t i) ^ 2) -
        ∑ i, x i ^ 2 * (1 - t i) ^ 2 := by
    rw [Nat.cast_sub hn]
    simp only [Nat.cast_one, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change _ ≤ ∑ i, x i ^ 2 * (((n - 1 : ℕ) : ℝ) * (1 + t i ^ 2) + 2 * t i)
  rw [halg]
  linarith

private theorem prod_le_one_of_sum_le_card {ι : Type*} (s : Finset ι) (f : ι → ℝ)
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

public theorem complex_offDiag_amgm_bound {n : ℕ} (hn : 2 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ^ 2 ≤
      ∏ i, (1 + (A i i).re ^ 2 + 2 * (A i i).re / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) := by
  let m : ℝ := ((n - 1 : ℕ) : ℝ)
  let t := fun i => (A i i).re
  let c := fun i => 1 + t i ^ 2 + 2 * t i / m
  let x := fun i => (Real.sqrt (c i))⁻¹
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < n - 1 by omega)
  have ht (i) : 0 ≤ t i := posSemidef_diag_re_nonneg hA i
  have hc (i) : 0 < c i := by
    have hi := ht i
    dsimp [c]
    positivity
  have hx (i) : 0 ≤ x i := by dsimp [x]; positivity
  have hxc (i) : x i ^ 2 * c i = 1 := by
    dsimp [x]
    rw [inv_pow, Real.sq_sqrt (hc i).le, inv_mul_cancel₀ (hc i).ne']
  have hsum : (∑ i, ∑ j ∈ Finset.univ.erase i, x i * x j * ‖1 - A i j‖ ^ 2) ≤
      (n : ℝ) * m := by
    calc
      _ ≤ ∑ i, x i ^ 2 * (m * (1 + t i ^ 2) + 2 * t i) :=
        weighted_offDiag_sum_le (by omega) hA x hx
      _ = ∑ _i : Fin n, m := by
        apply Finset.sum_congr rfl
        intro i _
        have he : m * (1 + t i ^ 2) + 2 * t i = m * c i := by
          dsimp [c]
          field_simp
        rw [he, mul_left_comm, hxc, mul_one]
      _ = _ := by simp
  let s := (Finset.univ : Finset (Fin n)).sigma (fun i => Finset.univ.erase i)
  let f := fun p : (i : Fin n) × Fin n => x p.1 * x p.2 * ‖1 - A p.1 p.2‖ ^ 2
  have hcard : s.card = n * (n - 1) := by
    simp [s, Finset.card_sigma]
  have hp : (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j * ‖1 - A i j‖ ^ 2) ≤ 1 := by
    have hp := prod_le_one_of_sum_le_card s f
      (by rw [hcard]; exact Nat.mul_pos (by omega) (by omega))
      (fun p _ => mul_nonneg (mul_nonneg (hx _) (hx _)) (sq_nonneg _))
      (by simpa [s, f, Finset.sum_sigma, hcard, Nat.cast_mul, m] using hsum)
    simpa [s, f, Finset.prod_sigma] using hp
  have hfactor : (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j * ‖1 - A i j‖ ^ 2) =
      (∏ i, (x i ^ 2) ^ (n - 1)) * (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ^ 2 := by
    calc
      _ = (∏ i, ∏ j ∈ Finset.univ.erase i, x i * x j) *
          (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖ ^ 2) := by
        simp only [Finset.prod_mul_distrib]
      _ = _ := by rw [prod_offDiag_mul]; simp only [Finset.prod_pow]
  rw [hfactor] at hp
  have hcancel : (∏ i, c i ^ (n - 1)) * (∏ i, (x i ^ 2) ^ (n - 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [← mul_pow, mul_comm (c _) (x _ ^ 2), hxc, one_pow, Finset.prod_const_one]
  have hmul := mul_le_mul_of_nonneg_left hp
    (Finset.prod_nonneg (s := Finset.univ) (fun i _ => pow_nonneg (hc i).le (n - 1)))
  rw [← mul_assoc, hcancel, one_mul, mul_one] at hmul
  exact hmul

public theorem goal_three : Goal 3 := by
  intro A hA
  apply goal_of_offDiag_le hA
  have h := complex_offDiag_amgm_bound (by omega : 2 ≤ 3) hA
  have he (t : ℝ) : 1 + t ^ 2 + 2 * t / ((3 - 1 : ℕ) : ℝ) = geomSum 3 t := by
    norm_num [geomSum, Finset.sum_range_succ]
    ring
  simp_rw [he] at h
  norm_num only [show 3 - 1 = 2 from rfl] at h
  rw [Finset.prod_pow] at h
  have hr : 0 ≤ ∏ i, geomSum 3 (A i i).re :=
    Finset.prod_nonneg fun i _ => geomSum_nonneg (posSemidef_diag_re_nonneg hA i)
  have hl : 0 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖ :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => norm_nonneg _
  nlinarith

end Problem1
