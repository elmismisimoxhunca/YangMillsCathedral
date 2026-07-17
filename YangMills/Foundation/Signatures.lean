/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Dimensions
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Euclidean and Minkowski quadratic forms

This module places two different quadratic forms on the same dimension-indexed coordinate-vector
type. It does not identify Euclidean and Minkowski spacetime, define analytic continuation, or
assert an Osterwalder–Schrader reconstruction.

Clay/Jaffe–Witten p. 5, §3 distinguishes `ℝ⁴` with Minkowski signature from Euclidean spacetime.
The convention with positive time weight and negative spatial weights is an explicit project
choice, not a verbatim sign convention from that paragraph.
-/

open scoped BigOperators

namespace YangMills.EuclideanDimension

/-- The algebraic real coordinate-vector space underlying a dimension-`d` spacetime chart.

No topology, metric, or signature is selected by this abbreviation. -/
abbrev CoordinateVector (d : EuclideanDimension) := d.CoordinateIndex → ℝ

/-- The coordinate basis vector with value one at `i` and zero elsewhere. -/
def basisVector (d : EuclideanDimension) (i : d.CoordinateIndex) : d.CoordinateVector :=
  fun j => if j = i then 1 else 0

/-- Coordinate zero, reserved as the time coordinate when a signature or reconstruction uses one. -/
def timeIndex (d : EuclideanDimension) : d.CoordinateIndex :=
  ⟨0, d.one_le⟩

/-- Embed a spatial coordinate index after the distinguished time coordinate. -/
def spatialIndexSucc (d : EuclideanDimension) (i : Fin d.spatialDimension) : d.CoordinateIndex :=
  ⟨i.val + 1, by
    have hi := i.isLt
    have hd := d.one_le
    simp only [spatialDimension] at hi
    omega⟩

/-- The positive-definite Euclidean quadratic form, with every coordinate weight equal to one. -/
def euclideanQuadraticForm (d : EuclideanDimension) : QuadraticForm ℝ d.CoordinateVector :=
  QuadraticMap.weightedSumSquares ℝ (fun _ => (1 : ℝ))

/-- The chosen mostly-minus Minkowski weight: positive on time and negative on spatial indices. -/
def minkowskiWeight (d : EuclideanDimension) (i : d.CoordinateIndex) : ℝ :=
  if i.val = 0 then 1 else -1

/-- The Minkowski quadratic form with convention `(+,-,…,-)`. -/
def minkowskiQuadraticForm (d : EuclideanDimension) : QuadraticForm ℝ d.CoordinateVector :=
  QuadraticMap.weightedSumSquares ℝ d.minkowskiWeight

/-- Evaluation of the Euclidean form as a sum of coordinate squares. -/
theorem euclideanQuadraticForm_apply (d : EuclideanDimension) (p : d.CoordinateVector) :
    d.euclideanQuadraticForm p = ∑ i, (p i) ^ 2 := by
  simp [euclideanQuadraticForm, QuadraticMap.weightedSumSquares_apply, pow_two]

/-- The Euclidean form is nonnegative. -/
theorem euclideanQuadraticForm_nonneg (d : EuclideanDimension) (p : d.CoordinateVector) :
    0 ≤ d.euclideanQuadraticForm p := by
  rw [d.euclideanQuadraticForm_apply]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Every Euclidean coordinate basis vector has quadratic value one. -/
@[simp] theorem euclideanQuadraticForm_basisVector
    (d : EuclideanDimension) (i : d.CoordinateIndex) :
    d.euclideanQuadraticForm (d.basisVector i) = 1 := by
  simp [euclideanQuadraticForm, basisVector, QuadraticMap.weightedSumSquares_apply]

/-- The selected Minkowski time basis vector has positive quadratic value. -/
@[simp] theorem minkowskiQuadraticForm_time_basisVector (d : EuclideanDimension) :
    d.minkowskiQuadraticForm (d.basisVector d.timeIndex) = 1 := by
  simp [minkowskiQuadraticForm, minkowskiWeight, basisVector, timeIndex,
    QuadraticMap.weightedSumSquares_apply]

/-- Every available Minkowski spatial basis vector has negative quadratic value. -/
@[simp] theorem minkowskiQuadraticForm_spatial_basisVector
    (d : EuclideanDimension) (i : Fin d.spatialDimension) :
    d.minkowskiQuadraticForm (d.basisVector (d.spatialIndexSucc i)) = -1 := by
  simp [minkowskiQuadraticForm, minkowskiWeight, basisVector, spatialIndexSucc,
    QuadraticMap.weightedSumSquares_apply]

/-- In Euclidean dimension one there are no spatial weights, so the two algebraic forms agree.
This does not identify Euclidean and Minkowski theories. -/
theorem one_euclideanQuadraticForm_eq_minkowskiQuadraticForm :
    one.euclideanQuadraticForm = one.minkowskiQuadraticForm := by
  ext p
  simp [euclideanQuadraticForm, minkowskiQuadraticForm, minkowskiWeight,
    QuadraticMap.weightedSumSquares_apply]

/-- From dimension two onward, a spatial basis direction witnesses that the Euclidean and
Minkowski forms are different. -/
theorem euclideanQuadraticForm_ne_minkowskiQuadraticForm
    (d : EuclideanDimension) (h : 2 ≤ d.value) :
    d.euclideanQuadraticForm ≠ d.minkowskiQuadraticForm := by
  intro forms_equal
  let spatial : Fin d.spatialDimension := ⟨0, by
    have hd := d.one_le
    simp only [spatialDimension]
    omega⟩
  have values_equal := congrArg
    (fun form : QuadraticForm ℝ d.CoordinateVector => form (d.basisVector (d.spatialIndexSucc spatial)))
    forms_equal
  norm_num at values_equal

end YangMills.EuclideanDimension
