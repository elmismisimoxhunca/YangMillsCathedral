/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite matrix multiplication as a real continuous bilinear map

The raw function carrier `Fin n → Fin n → ℂ` has a pointwise multiplication instance. This module
packages genuine matrix multiplication separately, preventing accidental substitution of pointwise
multiplication in differential and trace formulas. Continuity follows from finite dimensionality.
-/

namespace YangMills.Mathematics

open scoped BigOperators

noncomputable section

/-- Genuine finite matrix multiplication as a real bilinear map on the raw function carrier. -/
def finiteMatrixMulRealLinear (n : ℕ) :
    (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) →ₗ[ℝ]
      (Fin n → Fin n → ℂ) where
  toFun A := {
    toFun := fun B i j => ∑ k, A i k * B k j
    map_add' := by
      intro B C
      ext i j
      change (∑ k, A i k * (B k j + C k j)) =
        (∑ k, A i k * B k j) + ∑ k, A i k * C k j
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    map_smul' := by
      intro r B
      ext i j
      change (∑ k, A i k * ((r : ℂ) * B k j)) =
        (r : ℂ) * ∑ k, A i k * B k j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring }
  map_add' A B := by
    apply LinearMap.ext
    intro C
    ext i j
    change (∑ k, (A i k + B i k) * C k j) =
      (∑ k, A i k * C k j) + ∑ k, B i k * C k j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  map_smul' r A := by
    apply LinearMap.ext
    intro B
    ext i j
    change (∑ k, ((r : ℂ) * A i k) * B k j) =
      (r : ℂ) * ∑ k, A i k * B k j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Genuine finite matrix multiplication as a real continuous bilinear map. -/
def finiteMatrixMulContinuousBilinear (n : ℕ) :
    (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) →L[ℝ]
      (Fin n → Fin n → ℂ) := by
  let inner : (Fin n → Fin n → ℂ) →
      ((Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ)) :=
    fun A => LinearMap.toContinuousLinearMap (finiteMatrixMulRealLinear n A)
  let outer : (Fin n → Fin n → ℂ) →ₗ[ℝ]
      ((Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ)) := {
    toFun := inner
    map_add' := by
      intro A B
      apply ContinuousLinearMap.ext
      intro C
      ext i j
      change (∑ k, (A i k + B i k) * C k j) =
        (∑ k, A i k * C k j) + ∑ k, B i k * C k j
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    map_smul' := by
      intro r A
      apply ContinuousLinearMap.ext
      intro B
      ext i j
      change (∑ k, ((r : ℂ) * A i k) * B k j) =
        (r : ℂ) * ∑ k, A i k * B k j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring }
  exact LinearMap.toContinuousLinearMap outer

@[simp]
theorem finiteMatrixMulContinuousBilinear_apply
    (n : ℕ) (A B : Fin n → Fin n → ℂ) (i j : Fin n) :
    finiteMatrixMulContinuousBilinear n A B i j = ∑ k, A i k * B k j :=
  rfl

end

end YangMills.Mathematics
