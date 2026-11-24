module

public import Problem1.Reduction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Appendix B.3 and Issue #4: a roots-of-unity equality family and exact
counterexamples to termwise bounds, a complex extension of the real AM-GM
bound, and a reduction to pairwise constraints alone.
-/

open scoped BigOperators ComplexOrder

namespace Problem1

noncomputable section

@[expose] public def rootOmega (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

@[expose] public def rootsOfUnityVec (n : ℕ) (i : Fin n) : ℂ :=
  (rootOmega n) ^ (i : ℕ)

@[expose] public def rootsOfUnityMatrix (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (t : ℂ) * rootsOfUnityVec n i * star (rootsOfUnityVec n j)

public theorem rootsOfUnityMatrix_posSemidef {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (rootsOfUnityMatrix n t).PosSemidef := by
  let M : Matrix (Fin n) (Fin 1) ℂ := fun i _ => rootsOfUnityVec n i
  have h := (Matrix.posSemidef_self_mul_conjTranspose M).smul ht
  convert h using 1
  ext i j
  change (t : ℂ) * rootsOfUnityVec n i * star (rootsOfUnityVec n j) =
    (t : ℂ) * (∑ k : Fin 1, M i k * star (M j k))
  simp [M, mul_assoc]

private theorem rootOmega_primitive {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (rootOmega n) n := Complex.isPrimitiveRoot_exp n hn

public theorem rootsOfUnityMatrix_diag {n : ℕ} (t : ℝ) (i : Fin n) :
    rootsOfUnityMatrix n t i i = (t : ℂ) := by
  have hn : n ≠ 0 := by have := i.isLt; omega
  have hv : ‖rootsOfUnityVec n i‖ = 1 := by
    simp [rootsOfUnityVec, norm_pow, (rootOmega_primitive hn).norm'_eq_one hn]
  have he : rootsOfUnityVec n i * star (rootsOfUnityVec n i) = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
  change (t : ℂ) * rootsOfUnityVec n i * star (rootsOfUnityVec n i) = _
  rw [mul_assoc, he, mul_one]

public theorem rootsOfUnityMatrix_eq {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (_ht : 0 ≤ t) :
    (∏ i, ∏ j, ‖1 - rootsOfUnityMatrix n t i j‖) =
      ∏ i, ‖1 - (rootsOfUnityMatrix n t i i) ^ n‖ := by
  have hw := rootOmega_primitive (show n ≠ 0 by omega)
  have hs : IsPrimitiveRoot (star (rootOmega n)) n :=
    hw.map_of_injective (f := Complex.conjAe.toRingEquiv.toRingHom) (star_injective)
  apply Finset.prod_congr rfl
  intro i _
  have he : ((t : ℂ) * rootOmega n ^ (i : ℕ)) ^ n = (t : ℂ) ^ n := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, hw.pow_eq_one, one_pow, mul_one]
  -- Factor X^n - t^n using the conjugate primitive root and evaluate at 1.
  -- This avoids division by t and works unchanged when t = 0.
  have hp := X_pow_sub_C_eq_prod hs (by omega : 0 < n) he
  have hv := congrArg (Polynomial.eval (1 : ℂ)) hp
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hv
  rw [rootsOfUnityMatrix_diag, ← norm_prod]
  congr 1
  calc
    _ = ∏ j : Fin n, (1 - star (rootOmega n) ^ (j : ℕ) *
        ((t : ℂ) * rootOmega n ^ (i : ℕ))) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [rootsOfUnityMatrix, rootsOfUnityVec, star_pow, mul_comm]
    _ = _ := by
      exact (Fin.prod_univ_eq_prod_range
        (fun k => 1 - star (rootOmega n) ^ k * ((t : ℂ) * rootOmega n ^ (i : ℕ))) n).trans hv.symm

@[expose] public def allOnesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun _ _ => 1

public theorem allOnesMatrix_posSemidef (n : ℕ) : (allOnesMatrix n).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (fun (_ : Fin n) (_ : Fin 1) => (1 : ℂ))
  convert h using 1
  ext i j
  change (1 : ℂ) = ∑ _k : Fin 1, (1 : ℂ) * star (1 : ℂ)
  simp

public theorem not_termwise_abs_bound_three :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℂ), A.PosSemidef →
      (∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖A i j‖)) ≤
        ∏ i, geomSum 3 (A i i).re := by
  intro h
  have hbad := h (allOnesMatrix 3) (allOnesMatrix_posSemidef 3)
  norm_num [allOnesMatrix, geomSum, Finset.sum_range_succ,
    Finset.prod_const, Finset.card_erase_of_mem] at hbad

public theorem not_termwise_sqrt_bound_three :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℂ), A.PosSemidef →
      (∏ i, ∏ j ∈ Finset.univ.erase i,
        (1 + Real.sqrt ((A i i).re * (A j j).re))) ≤
          ∏ i, geomSum 3 (A i i).re := by
  intro h
  have hbad := h (allOnesMatrix 3) (allOnesMatrix_posSemidef 3)
  norm_num [allOnesMatrix, geomSum, Finset.sum_range_succ,
    Finset.prod_const, Finset.card_erase_of_mem] at hbad

public theorem not_real_amgm_strengthening_complex_three :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℂ), A.PosSemidef →
      (∀ i, (A i i).re ≤ 1) →
        (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) ≤
          ∏ i, (1 + (A i i).re / 2) ^ 2 := by
  intro h
  let A := rootsOfUnityMatrix 3 (1 / 2)
  have hA : A.PosSemidef := rootsOfUnityMatrix_posSemidef (by norm_num)
  have hdiag (i : Fin 3) : A i i = ((1 / 2 : ℝ) : ℂ) := rootsOfUnityMatrix_diag _ _
  have hnorm (i : Fin 3) : ‖1 - A i i‖ = (1 / 2 : ℝ) := by
    rw [hdiag, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have heq := rootsOfUnityMatrix_eq (by omega : 1 ≤ 3) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change (∏ i, ∏ j, ‖1 - A i j‖) = ∏ i, ‖1 - (A i i) ^ 3‖ at heq
  rw [prod_diag_mul_offDiag] at heq
  simp_rw [norm_one_sub_pow_eq hA.diag_nonneg, hnorm, hdiag] at heq
  norm_num [geomSum, Finset.sum_range_succ] at heq
  have hoff : (∏ i, ∏ j ∈ Finset.univ.erase i, ‖1 - A i j‖) = (343 / 64 : ℝ) := by
    linarith
  have hbad := h A hA (fun i => by rw [hdiag]; norm_num)
  simp_rw [hdiag] at hbad
  norm_num at hbad
  linarith [hoff]

@[expose] public def pairwiseCounterexample : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then 1 else -1

public theorem pairwiseCounterexample_isHermitian : pairwiseCounterexample.IsHermitian := by
  ext i j
  change (if j = i then (1 : ℝ) else -1) = if i = j then 1 else -1
  simp [eq_comm]

public theorem pairwiseCounterexample_diag_nonneg (i : Fin 3) :
    0 ≤ pairwiseCounterexample i i := by simp [pairwiseCounterexample]

public theorem pairwiseCounterexample_two_by_two (i j : Fin 3) :
    (pairwiseCounterexample i j) ^ 2 ≤
      pairwiseCounterexample i i * pairwiseCounterexample j j := by
  by_cases h : i = j <;> simp [pairwiseCounterexample, h]

public theorem pairwiseCounterexample_not_posSemidef : ¬ pairwiseCounterexample.PosSemidef := by
  intro h
  have hbad := h.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  norm_num [dotProduct, Matrix.mulVec, pairwiseCounterexample, Fin.sum_univ_succ] at hbad

public theorem pairwiseCounterexample_violates_offDiag :
    (∏ i : Fin 3, geomSum 3 (pairwiseCounterexample i i)) <
      ∏ i : Fin 3, ∏ j ∈ Finset.univ.erase i, |1 - pairwiseCounterexample i j| := by
  have he (i : Fin 3) :
      (∏ j ∈ Finset.univ.erase i, |1 - pairwiseCounterexample i j|) = 4 := by
    calc
      _ = ∏ _j ∈ Finset.univ.erase i, (2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        norm_num [pairwiseCounterexample, Ne.symm hji]
      _ = _ := by norm_num
  simp_rw [he]
  norm_num [pairwiseCounterexample, geomSum, Finset.sum_range_succ]

public theorem not_offDiag_from_two_by_two_only :
    ¬ ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), M.IsHermitian →
      (∀ i, 0 ≤ M i i) → (∀ i j, (M i j) ^ 2 ≤ M i i * M j j) →
        (∏ i, ∏ j ∈ Finset.univ.erase i, |1 - M i j|) ≤ ∏ i, geomSum 3 (M i i) := by
  intro h
  exact (not_le_of_gt pairwiseCounterexample_violates_offDiag)
    (h pairwiseCounterexample pairwiseCounterexample_isHermitian
      pairwiseCounterexample_diag_nonneg pairwiseCounterexample_two_by_two)

end

end Problem1
