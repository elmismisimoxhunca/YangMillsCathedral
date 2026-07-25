/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTranslation

/-!
# Nonzero spatial rays for Schwinger clustering

OS-I `(E4)` separates one test cluster along `λa` with `a = (0, a⃗)` spatial and `λ → +∞`.
This module packages a unit spatial direction, constructs a canonical direction whenever spacetime
has at least one spatial coordinate, and proves that its ray has zero Euclidean-time component and
norm tending to infinity.

Dimension one is handled explicitly: after selecting its sole coordinate as time, no unit spatial
direction exists. Thus later clustering requirements cannot become silently vacuous or
ill-typed across dimensions. This module still states no cluster-factorization limit.
-/

namespace YangMills

/-- A normalized, hence nonzero, Euclidean displacement direction orthogonal to the selected time
coordinate. -/
structure EuclideanUnitSpatialDirection (d : EuclideanDimension) where
  /-- The underlying Euclidean spacetime vector. -/
  vector : d.Spacetime
  /-- A spatial direction has zero selected time component. -/
  time_eq_zero : vector (euclideanTimeCoordinate d) = 0
  /-- Normalization prevents the zero direction and fixes ray parametrization. -/
  norm_eq_one : ‖vector‖ = 1

/-- The canonical second-coordinate spatial direction whenever `d ≥ 2`. -/
noncomputable def canonicalEuclideanUnitSpatialDirection
    (d : EuclideanDimension) (h : 2 ≤ d.value) : EuclideanUnitSpatialDirection d where
  vector := EuclideanSpace.single (⟨1, h⟩ : d.CoordinateIndex) 1
  time_eq_zero := by
    simp [euclideanTimeCoordinate]
  norm_eq_one := by
    simp

/-- Four-dimensional Euclidean spacetime has the canonical nonzero spatial direction needed by the
Clay-dimensional clustering surface. -/
noncomputable def fourDimensionalCanonicalSpatialDirection :
    EuclideanUnitSpatialDirection EuclideanDimension.four :=
  canonicalEuclideanUnitSpatialDirection EuclideanDimension.four (by decide)

/-- A unit spatial direction is genuinely nonzero. -/
theorem EuclideanUnitSpatialDirection.vector_ne_zero
    {d : EuclideanDimension} (v : EuclideanUnitSpatialDirection d) : v.vector ≠ 0 := by
  intro hzero
  have hnorm := v.norm_eq_one
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- One-dimensional Euclidean spacetime has no spatial direction after its only coordinate is
selected as time. -/
theorem oneDimensional_no_unitSpatialDirection :
    IsEmpty (EuclideanUnitSpatialDirection EuclideanDimension.one) := by
  constructor
  intro v
  have hvector : v.vector = 0 := by
    ext i
    have hi : i = euclideanTimeCoordinate EuclideanDimension.one := by
      apply Fin.ext
      simp [euclideanTimeCoordinate]
    rw [hi, v.time_eq_zero]
    rfl
  exact v.vector_ne_zero hvector

/-- The displacement at real ray parameter `λ`. -/
noncomputable def euclideanSpatialRayDisplacement
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    d.Spacetime :=
  scale • v.vector

/-- Every point of the ray has zero selected Euclidean-time component. -/
@[simp] theorem euclideanSpatialRayDisplacement_time
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    euclideanSpatialRayDisplacement d v scale (euclideanTimeCoordinate d) = 0 := by
  simp [euclideanSpatialRayDisplacement, v.time_eq_zero]

/-- Ray distance from the origin is exactly `|λ|` because the direction is normalized. -/
@[simp] theorem norm_euclideanSpatialRayDisplacement
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    ‖euclideanSpatialRayDisplacement d v scale‖ = |scale| := by
  unfold euclideanSpatialRayDisplacement
  rw [norm_smul, v.norm_eq_one, mul_one]
  exact Real.norm_eq_abs scale

/-- The normalized spatial ray genuinely escapes to infinity as `λ → +∞`. -/
theorem tendsto_norm_euclideanSpatialRayDisplacement_atTop
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) :
    Filter.Tendsto (fun scale : ℝ => ‖euclideanSpatialRayDisplacement d v scale‖)
      Filter.atTop Filter.atTop := by
  simpa using (Filter.tendsto_abs_atTop_atTop :
    Filter.Tendsto (fun scale : ℝ => |scale|) Filter.atTop Filter.atTop)

/-- Translate an unrestricted finite sequence along one exact spatial ray. -/
noncomputable def translateScalarFiniteSchwartzSequenceAlongSpatialRay
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ)
    (f : ScalarFiniteSchwartzSequence d) : ScalarFiniteSchwartzSequence d :=
  translateScalarFiniteSchwartzSequence d (euclideanSpatialRayDisplacement d v scale) f

@[simp] theorem translateScalarFiniteSchwartzSequenceAlongSpatialRay_support
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ)
    (f : ScalarFiniteSchwartzSequence d) :
    (translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale f).support = f.support :=
  rfl

@[simp] theorem translateScalarFiniteSchwartzSequenceAlongSpatialRay_component
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ)
    (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale f).component n =
      translateScalarSchwartzTestFunction d
        (euclideanSpatialRayDisplacement d v scale) (f.component n) :=
  rfl

end YangMills
