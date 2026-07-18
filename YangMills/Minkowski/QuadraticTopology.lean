/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareKinematics

/-!
# Topology of the Minkowski quadratic form

A small reusable bridge between the algebraic mostly-minus form and the standard
finite-dimensional topology. This is shared by locality and joint spectral support; neither
physical axiom is imported by the other.
-/

namespace YangMills.Minkowski

/-- The Minkowski quadratic form is continuous on the finite-dimensional coordinate carrier. -/
theorem continuous_minkowskiQuadraticForm (d : EuclideanDimension) :
    Continuous d.minkowskiQuadraticForm := by
  change Continuous (fun p : Spacetime d => d.minkowskiQuadraticForm p)
  simp only [EuclideanDimension.minkowskiQuadraticForm,
    QuadraticMap.weightedSumSquares_apply]
  apply continuous_finsetSum Finset.univ
  intro i _
  fun_prop

/-- The mostly-minus invariant square is at most the square of the energy coordinate. -/
theorem minkowskiQuadraticForm_le_timeSquare
    (d : EuclideanDimension) (p : Spacetime d) :
    d.minkowskiQuadraticForm p ≤ (p d.timeIndex) ^ 2 := by
  rw [EuclideanDimension.minkowskiQuadraticForm,
    QuadraticMap.weightedSumSquares_apply]
  calc
    (∑ i, d.minkowskiWeight i • (p i * p i)) ≤
        ∑ i, if i = d.timeIndex then (p d.timeIndex) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = d.timeIndex
      · subst i
        simp [EuclideanDimension.minkowskiWeight, EuclideanDimension.timeIndex, pow_two]
      · have hval : i.val ≠ 0 := by
          intro hz
          apply hi
          apply Fin.ext
          simpa [EuclideanDimension.timeIndex] using hz
        simp [EuclideanDimension.minkowskiWeight, hval, hi]
        exact mul_self_nonneg _
    _ = (p d.timeIndex) ^ 2 := by simp

end YangMills.Minkowski
