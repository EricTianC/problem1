import Problem1.Statement

open scoped BigOperators ComplexOrder

namespace Problem1

private theorem norm_sq_entry_le_diag_mul (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) : ‖A 0 1‖ ^ 2 ≤ (A 0 0).re * (A 1 1).re := by
  let a := (A 0 0).re
  let b := (A 1 1).re
  let z := A 0 1
  have h00 := Complex.nonneg_iff.mp (hA.diag_nonneg (i := 0))
  have h11 := Complex.nonneg_iff.mp (hA.diag_nonneg (i := 1))
  have hconj : A 1 0 = (starRingEnd ℂ) z := (hA.isHermitian.apply 1 0).symm
  have hquad (r t : ℝ) : 0 ≤ a * r ^ 2 * ‖z‖ ^ 2 - 2 * r * t * ‖z‖ ^ 2 + b * t ^ 2 := by
    have h := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ![(r : ℂ) * z, -(t : ℂ)])).1
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hconj, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, h00.2.symm, h11.2.symm] at h
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [a, b, z] at h ⊢
    nlinarith only [h]
  change ‖z‖ ^ 2 ≤ a * b
  by_cases ha : a = 0
  · -- This choice forces the off-diagonal entry to vanish when a = 0.
    have h := hquad (b + 1) (‖z‖ ^ 2)
    rw [ha] at h ⊢
    have hsq : (‖z‖ ^ 2) ^ 2 ≤ 0 := by
      nlinarith only [h, mul_nonneg h11.1 (sq_nonneg (‖z‖ ^ 2))]
    have hz : ‖z‖ ^ 2 = 0 := by
      simpa using le_antisymm hsq (sq_nonneg (‖z‖ ^ 2))
    simp [hz]
  · have ha_pos : 0 < a := lt_of_le_of_ne h00.1 (Ne.symm ha)
    have h : 0 ≤ a * (a * b - ‖z‖ ^ 2) := by nlinarith only [hquad 1 a]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h ha_pos)

theorem norm_one_sub_sq_le (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : ‖z‖ ^ 2 ≤ a * b) : ‖1 - z‖ ^ 2 ≤ (1 + a) * (1 + b) := by
  have hnorm : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    have hone : ‖(1 : ℂ)‖ = 1 := by
      simpa only [Complex.ofReal_one] using Complex.norm_of_nonneg (r := 1) zero_le_one
    simpa only [hone] using norm_sub_le (1 : ℂ) z
  have hlinear : 2 * ‖z‖ ≤ a + b := by
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) (norm_nonneg _)) (add_nonneg ha hb)).mp
    nlinarith [sq_nonneg (a - b)]
  calc
    ‖1 - z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg _))).mpr hnorm
    _ ≤ (1 + a) * (1 + b) := by nlinarith

private theorem norm_one_sub_sq_factor {z : ℂ} (hz : 0 ≤ z) :
    ‖1 - z ^ 2‖ = ‖1 - z‖ * (1 + z.re) := by
  have hre : z.im = 0 := (Complex.nonneg_iff.mp hz).2.symm
  have hcoe : (↑(1 + z.re) : ℂ) = 1 + z := by
    apply Complex.ext <;> simp [hre]
  rw [show 1 - z ^ 2 = (1 - z) * (1 + z) by ring, Complex.norm_mul, ← hcoe,
    Complex.norm_of_nonneg (add_nonneg zero_le_one (Complex.nonneg_iff.mp hz).1)]

/-- The seminar inequality for complex positive semidefinite matrices of size two. -/
theorem goal_two : Goal 2 := by
  intro A hA
  have h00 : 0 ≤ A 0 0 := hA.diag_nonneg
  have h11 : 0 ≤ A 1 1 := hA.diag_nonneg
  have hconj : ‖1 - A 1 0‖ = ‖1 - A 0 1‖ := by
    simpa only [map_sub, map_one, starRingEnd_apply, hA.isHermitian.apply 1 0] using
      Complex.norm_conj (1 - A 0 1)
  have hoff := norm_one_sub_sq_le (A 0 1) (Complex.nonneg_iff.mp h00).1
    (Complex.nonneg_iff.mp h11).1 (norm_sq_entry_le_diag_mul A hA)
  simp only [Fin.prod_univ_two, hconj, norm_one_sub_sq_factor h00, norm_one_sub_sq_factor h11]
  calc
    (‖1 - A 0 0‖ * ‖1 - A 0 1‖) * (‖1 - A 0 1‖ * ‖1 - A 1 1‖) =
        (‖1 - A 0 0‖ * ‖1 - A 1 1‖) * ‖1 - A 0 1‖ ^ 2 := by ring
    _ ≤ (‖1 - A 0 0‖ * ‖1 - A 1 1‖) * ((1 + (A 0 0).re) * (1 + (A 1 1).re)) :=
      mul_le_mul_of_nonneg_left hoff (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖1 - A 0 0‖ * (1 + (A 0 0).re)) * (‖1 - A 1 1‖ * (1 + (A 1 1).re)) := by ring

#print axioms norm_one_sub_sq_le
#print axioms goal_two

end Problem1
