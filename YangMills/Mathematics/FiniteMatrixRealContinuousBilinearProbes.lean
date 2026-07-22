/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteMatrixRealContinuousBilinear

namespace YangMills.Mathematics.FiniteMatrixRealContinuousBilinear.Probes

open scoped BigOperators

noncomputable section

/-- A single upper off-diagonal matrix unit. -/
def upper : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else 0

/-- The matching lower off-diagonal matrix unit. -/
def lower : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = 1 ∧ j = 0 then 1 else 0

/-- Genuine multiplication includes the contracted middle index. -/
theorem exact_contracted_coordinate (i j : Fin 2) :
    finiteMatrixMulContinuousBilinear 2 upper lower i j =
      ∑ k, upper i k * lower k j :=
  rfl

/-- Off-diagonal matrix units contribute to the trace of their genuine product. -/
theorem offDiagonal_product_trace :
    Matrix.trace (finiteMatrixMulContinuousBilinear 2 upper lower) = 1 := by
  simp [Matrix.trace, finiteMatrixMulContinuousBilinear_apply, upper, lower, Fin.sum_univ_two]

/-- Pointwise multiplication would erase the same off-diagonal contraction and is rejected. -/
theorem pointwise_substitution_blocked :
    Matrix.trace (finiteMatrixMulContinuousBilinear 2 upper lower) ≠
      Matrix.trace (upper * lower) := by
  simp [Matrix.trace, finiteMatrixMulContinuousBilinear_apply, upper, lower, Fin.sum_univ_two]

end

end YangMills.Mathematics.FiniteMatrixRealContinuousBilinear.Probes
