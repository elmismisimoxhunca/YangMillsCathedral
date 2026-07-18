/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSpatialRay
import YangMills.Euclidean.SchwingerTestSequence
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for Euclidean spatial rays

The probes exhibit a genuine four-dimensional direction and escaping ray, reject any such direction
in dimension one, and retain the nonzero bump under every ray translation.
-/

namespace YangMills.Euclidean.SchwingerSpatialRay.Probes

/-- The four-dimensional checker surface has an explicit unit spatial direction. -/
noncomputable def explicit_four_dimensional_direction :
    EuclideanUnitSpatialDirection EuclideanDimension.four :=
  fourDimensionalCanonicalSpatialDirection

/-- The explicit four-dimensional direction has zero selected time component. -/
theorem four_direction_time_zero :
    explicit_four_dimensional_direction.vector
      (euclideanTimeCoordinate EuclideanDimension.four) = 0 :=
  explicit_four_dimensional_direction.time_eq_zero

/-- The explicit four-dimensional direction is normalized. -/
theorem four_direction_norm_one :
    ‖explicit_four_dimensional_direction.vector‖ = 1 :=
  explicit_four_dimensional_direction.norm_eq_one

/-- The explicit four-dimensional direction is genuinely nonzero. -/
theorem four_direction_ne_zero :
    explicit_four_dimensional_direction.vector ≠ 0 :=
  explicit_four_dimensional_direction.vector_ne_zero

/-- Dimension one has no spatial direction after its sole coordinate is selected as time. -/
theorem dimension_one_direction_blocked :
    IsEmpty (EuclideanUnitSpatialDirection EuclideanDimension.one) :=
  oneDimensional_no_unitSpatialDirection

/-- The ray's selected time component remains zero for every real scale. -/
theorem exact_ray_time_zero
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    euclideanSpatialRayDisplacement d v scale (euclideanTimeCoordinate d) = 0 :=
  euclideanSpatialRayDisplacement_time d v scale

/-- The ray norm records the exact scale magnitude. -/
theorem exact_ray_norm
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    ‖euclideanSpatialRayDisplacement d v scale‖ = |scale| :=
  norm_euclideanSpatialRayDisplacement d v scale

/-- The four-dimensional ray at scale one is nonzero. -/
theorem four_ray_at_one_ne_zero :
    euclideanSpatialRayDisplacement EuclideanDimension.four
      explicit_four_dimensional_direction 1 ≠ 0 := by
  intro hzero
  have hnorm := norm_euclideanSpatialRayDisplacement EuclideanDimension.four
    explicit_four_dimensional_direction 1
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The ray genuinely escapes to infinity; a constant or zero displacement cannot pass. -/
theorem ray_norm_tends_to_infinity
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) :
    Filter.Tendsto (fun scale : ℝ => ‖euclideanSpatialRayDisplacement d v scale‖)
      Filter.atTop Filter.atTop :=
  tendsto_norm_euclideanSpatialRayDisplacement_atTop d v

/-- Translating the singleton bump along a spatial ray preserves its exact support. -/
theorem ray_translated_bump_exact_support
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    (translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support =
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence.support :=
  rfl

/-- The nonzero bump's arity-one support survives every spatial-ray translation. -/
theorem ray_translated_bump_one_mem_support
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    1 ∈ (translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support := by
  rw [translateScalarFiniteSchwartzSequenceAlongSpatialRay_support]
  rw [_root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.forgotten_singleton_bump_support]
  simp

/-- Omitting the ray-translated bump's exact support is impossible. -/
theorem omitted_ray_translated_bump_support_blocked
    (d : EuclideanDimension) (v : EuclideanUnitSpatialDirection d) (scale : ℝ)
    (homitted : 1 ∉ (translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support) : False :=
  homitted (ray_translated_bump_one_mem_support d v scale)

end YangMills.Euclidean.SchwingerSpatialRay.Probes
