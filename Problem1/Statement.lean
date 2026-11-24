module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators ComplexOrder

namespace Problem1

/-- The seminar problem, recorded as a proposition, not as a proved declaration. -/
@[expose] public def Goal (n : ℕ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
    (∏ i, ∏ j, ‖1 - A i j‖) ≤ ∏ i, ‖1 - (A i i) ^ n‖

end Problem1
