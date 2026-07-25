/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Foundation.Signatures

/-!
# Polarization of the mostly-minus Minkowski quadratic form

Streater–Wightman printed p. 9, equations `(1-4)`–`(1-6)`, fixes the four-dimensional mostly-minus
scalar product. This file develops the corresponding finite-coordinate bilinear form in every project
dimension `1 ≤ d ≤ 4`, proves its exact relationship with the existing quadratic form, and derives
preservation of the bilinear form from preservation of the quadratic form.

The zero-time nonpositivity theorem is reusable future-cone infrastructure. No Lorentz-group closure,
Poincaré cover, quantum theory, or mass gap is constructed here.
-/

namespace YangMills
namespace Minkowski

open scoped BigOperators

/-- The real symmetric mostly-minus Minkowski bilinear form in exact project coordinates. -/
def minkowskiBilinearForm (d : EuclideanDimension)
    (x y : d.CoordinateVector) : ℝ :=
  ∑ i, d.minkowskiWeight i * x i * y i

/-- Exact coordinate evaluation of the existing Minkowski quadratic form. -/
theorem minkowskiQuadraticForm_apply (d : EuclideanDimension) (x : d.CoordinateVector) :
    d.minkowskiQuadraticForm x =
      ∑ i, d.minkowskiWeight i * (x i) ^ 2 := by
  simp [EuclideanDimension.minkowskiQuadraticForm,
    QuadraticMap.weightedSumSquares_apply, pow_two]

/-- The bilinear form evaluated twice on one vector is the existing quadratic form. -/
@[simp]
theorem minkowskiBilinearForm_self (d : EuclideanDimension) (x : d.CoordinateVector) :
    minkowskiBilinearForm d x x = d.minkowskiQuadraticForm x := by
  rw [minkowskiQuadraticForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The bilinear form is symmetric. -/
theorem minkowskiBilinearForm_comm (d : EuclideanDimension)
    (x y : d.CoordinateVector) :
    minkowskiBilinearForm d x y = minkowskiBilinearForm d y x := by
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pairing the time basis on the left extracts the exact time coordinate. -/
@[simp]
theorem minkowskiBilinearForm_timeBasis_left
    (d : EuclideanDimension) (x : d.CoordinateVector) :
    minkowskiBilinearForm d (d.basisVector d.timeIndex) x = x d.timeIndex := by
  simp [minkowskiBilinearForm, EuclideanDimension.basisVector,
    EuclideanDimension.timeIndex, EuclideanDimension.minkowskiWeight]

/-- Pairing the time basis on the right extracts the exact time coordinate. -/
@[simp]
theorem minkowskiBilinearForm_timeBasis_right
    (d : EuclideanDimension) (x : d.CoordinateVector) :
    minkowskiBilinearForm d x (d.basisVector d.timeIndex) = x d.timeIndex := by
  rw [minkowskiBilinearForm_comm]
  exact minkowskiBilinearForm_timeBasis_left d x

/-- Exact real polarization identity, with no Hermitian conjugation. -/
theorem minkowskiQuadraticForm_polarization
    (d : EuclideanDimension) (x y : d.CoordinateVector) :
    d.minkowskiQuadraticForm (x + y) - d.minkowskiQuadraticForm x -
      d.minkowskiQuadraticForm y = 2 * minkowskiBilinearForm d x y := by
  rw [minkowskiQuadraticForm_apply, minkowskiQuadraticForm_apply,
    minkowskiQuadraticForm_apply]
  simp only [Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [show 2 * minkowskiBilinearForm d x y =
    ∑ i, 2 * (d.minkowskiWeight i * x i * y i) by
      simp [minkowskiBilinearForm, Finset.mul_sum]]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val = 0
  · simp [EuclideanDimension.minkowskiWeight, hi]
    ring
  · simp [EuclideanDimension.minkowskiWeight, hi]
    ring

/-- A vector whose time coordinate vanishes has nonpositive mostly-minus quadratic value. -/
theorem minkowskiQuadraticForm_nonpos_of_time_eq_zero
    (d : EuclideanDimension) {x : d.CoordinateVector}
    (hx : x d.timeIndex = 0) :
    d.minkowskiQuadraticForm x ≤ 0 := by
  rw [minkowskiQuadraticForm_apply]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : i.val = 0
  · have ieq : i = d.timeIndex := Fin.ext hi
    subst i
    simp [hx]
  · simp [EuclideanDimension.minkowskiWeight, hi, sq_nonneg]

/-- Any real-linear map preserving the exact Minkowski quadratic form also preserves its polarized
bilinear form. -/
theorem minkowskiBilinearForm_map_eq_of_quadratic_preserving
    (d : EuclideanDimension)
    (linear : d.CoordinateVector →ₗ[ℝ] d.CoordinateVector)
    (preservesQuadratic : ∀ x,
      d.minkowskiQuadraticForm (linear x) = d.minkowskiQuadraticForm x)
    (x y : d.CoordinateVector) :
    minkowskiBilinearForm d (linear x) (linear y) =
      minkowskiBilinearForm d x y := by
  have polarizedImage := minkowskiQuadraticForm_polarization d (linear x) (linear y)
  have polarizedSource := minkowskiQuadraticForm_polarization d x y
  rw [← linear.map_add, preservesQuadratic, preservesQuadratic, preservesQuadratic]
    at polarizedImage
  linarith

end Minkowski
end YangMills
