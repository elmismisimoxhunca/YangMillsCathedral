/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerOrderedTestSpace
import YangMills.Minkowski.WightmanTubeGeometry

/-!
# Reverse-ordered Wick-rotation geometry

OS-I printed p. 98, equation `(5.1)`, supplies the imaginary-time continuation convention. Strict
OS test configurations use increasing positive Euclidean times, while the Wightman backward
tube uses consecutive differences `zᵢ-zᵢ₊₁ = ξᵢ-iηᵢ` with `ηᵢ` future-directed. This module makes
the required reversal explicit: Euclidean point order is reversed before sending time `τ` to
`-iτ`. It proves that every strictly increasing Euclidean configuration lands in the exact
Wightman backward tube.

This is only geometric wiring. It does not identify Euclidean and Minkowski carriers, equate
correlators, analytically continue a distribution, reconstruct a Hilbert space, or construct any
physical theory.
-/

namespace YangMills.Reconstruction

open Minkowski

/-- Reverse Euclidean point order and Wick-rotate only the distinguished time coordinate by
`τ ↦ -iτ`. -/
def reverseWickRotateEuclideanConfiguration
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d n) :
    Fin n → ComplexifiedSpacetime d :=
  fun j i =>
    if i = euclideanTimeCoordinate d then
      -Complex.I * Complex.ofReal (x j.rev i)
    else
      Complex.ofReal (x j.rev i)

/-- Wick rotation without reversing point order, retained only for hostile comparison. -/
def unreversedWickRotateEuclideanConfiguration
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d n) :
    Fin n → ComplexifiedSpacetime d :=
  fun j i =>
    if i = euclideanTimeCoordinate d then
      -Complex.I * Complex.ofReal (x j i)
    else
      Complex.ofReal (x j i)

/-- Consecutive relative coordinates formed without the required point reversal. -/
def unreversedWickRotatedRelativeCoordinates
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d (n + 1)) :
    Fin n → ComplexifiedSpacetime d :=
  fun j i => unreversedWickRotateEuclideanConfiguration d (n + 1) x j.castSucc i -
    unreversedWickRotateEuclideanConfiguration d (n + 1) x j.succ i

/-- Consecutive relative coordinates of the reverse Wick-rotated configuration. -/
def reverseWickRotatedRelativeCoordinates
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d (n + 1)) :
    Fin n → ComplexifiedSpacetime d :=
  fun j i => reverseWickRotateEuclideanConfiguration d (n + 1) x j.castSucc i -
    reverseWickRotateEuclideanConfiguration d (n + 1) x j.succ i

/-- The imaginary part of each relative coordinate is exactly the negative reversed Euclidean time
difference, with no imaginary spatial component. -/
theorem negative_imaginary_reverseWickRotatedRelativeCoordinates
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d (n + 1))
    (j : Fin n) :
    -complexifiedSpacetimeImaginaryPart
      (reverseWickRotatedRelativeCoordinates d n x j) =
      (x j.castSucc.rev (euclideanTimeCoordinate d) -
        x j.succ.rev (euclideanTimeCoordinate d)) •
          d.basisVector d.timeIndex := by
  funext i
  by_cases hi : i = euclideanTimeCoordinate d
  · subst i
    simp [reverseWickRotatedRelativeCoordinates,
      reverseWickRotateEuclideanConfiguration,
      complexifiedSpacetimeImaginaryPart,
      EuclideanDimension.basisVector, EuclideanDimension.timeIndex,
      euclideanTimeCoordinate]
    ring
  · have hitime : i ≠ d.timeIndex := by
      simpa [euclideanTimeCoordinate, EuclideanDimension.timeIndex] using hi
    simp [reverseWickRotatedRelativeCoordinates,
      reverseWickRotateEuclideanConfiguration,
      complexifiedSpacetimeImaginaryPart,
      EuclideanDimension.basisVector, hi, hitime]

/-- Reversal changes increasing Euclidean labels into the decreasing order needed by consecutive
Wightman differences. -/
theorem reverse_successor_time_lt_reverse_castSucc_time
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d (n + 1))
    (hordered : x ∈ strictPositiveTimeOrderedConfigurationSet d (n + 1))
    (j : Fin n) :
    x j.succ.rev (euclideanTimeCoordinate d) <
      x j.castSucc.rev (euclideanTimeCoordinate d) := by
  apply hordered.2
  rw [Fin.rev_lt_rev]
  exact Fin.castSucc_lt_succ

/-- Explicit strictly positive, increasing Euclidean-time configuration with zero spatial
coordinates. -/
def standardStrictEuclideanConfiguration
    (d : EuclideanDimension) (n : ℕ) : EuclideanNPointSpace d n :=
  fun j => WithLp.toLp 2 (fun i =>
    if i = euclideanTimeCoordinate d then (j.val : ℝ) + 1 else 0)

/-- The explicit standard configuration is genuinely strict and ordered. -/
theorem standardStrictEuclideanConfiguration_mem
    (d : EuclideanDimension) (n : ℕ) :
    standardStrictEuclideanConfiguration d n ∈
      strictPositiveTimeOrderedConfigurationSet d n := by
  constructor
  · intro i
    simp [standardStrictEuclideanConfiguration]
    positivity
  · intro i j hij
    simp [standardStrictEuclideanConfiguration]
    exact_mod_cast hij

/-- Without point reversal, the explicit increasing two-point configuration has the wrong tube
sign. -/
theorem unreversed_standard_twoPoint_not_mem_backwardTube
    (d : EuclideanDimension) :
    unreversedWickRotatedRelativeCoordinates d 1
      (standardStrictEuclideanConfiguration d 2) ∉ wightmanBackwardTube d 1 := by
  intro hwrong
  have htime := (hwrong 0).1
  simp [unreversedWickRotatedRelativeCoordinates,
    unreversedWickRotateEuclideanConfiguration,
    standardStrictEuclideanConfiguration,
    complexifiedSpacetimeImaginaryPart,
    EuclideanDimension.timeIndex, euclideanTimeCoordinate] at htime
  norm_num at htime

/-- Every strict increasing Euclidean configuration maps to the exact Wightman backward tube after
explicit reversal and Wick rotation. -/
theorem reverseWickRotatedRelativeCoordinates_mem_backwardTube
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d (n + 1))
    (hordered : x ∈ strictPositiveTimeOrderedConfigurationSet d (n + 1)) :
    reverseWickRotatedRelativeCoordinates d n x ∈ wightmanBackwardTube d n := by
  intro j
  rw [negative_imaginary_reverseWickRotatedRelativeCoordinates]
  let Δτ : ℝ := x j.castSucc.rev (euclideanTimeCoordinate d) -
    x j.succ.rev (euclideanTimeCoordinate d)
  have hΔτ : 0 < Δτ := sub_pos.mpr
    (reverse_successor_time_lt_reverse_castSucc_time d n x hordered j)
  constructor
  · simp [Δτ, EuclideanDimension.basisVector,
      EuclideanDimension.timeIndex, hΔτ]
  · change 0 < d.minkowskiQuadraticForm (Δτ • d.basisVector d.timeIndex)
    rw [QuadraticMap.map_smul, d.minkowskiQuadraticForm_time_basisVector]
    simpa using mul_pos hΔτ hΔτ

end YangMills.Reconstruction
