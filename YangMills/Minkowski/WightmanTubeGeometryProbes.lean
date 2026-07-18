/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubeGeometry

/-!
# Hostile probes for Wightman tube geometry

The probes lock openness, strictness, nonemptiness in dimensions 1–4, and the source's negative
imaginary sign. No holomorphic function or boundary value is constructed.
-/

namespace YangMills.Minkowski.WightmanTubeGeometry.Probes

/-- Every supported dimension and relative arity has an open tube. -/
theorem exact_tube_open (d : EuclideanDimension) (n : ℕ) :
    IsOpen (wightmanBackwardTube d n) :=
  isOpen_wightmanBackwardTube d n

/-- Every supported dimension and relative arity has an explicit tube point. -/
theorem exact_tube_nonempty (d : EuclideanDimension) (n : ℕ) :
    (wightmanBackwardTube d n).Nonempty :=
  wightmanBackwardTube_nonempty d n

/-- Four-dimensional two-relative-coordinate tube geometry is nonvacuous. -/
theorem four_dimensional_two_coordinate_tube_nonempty :
    (wightmanBackwardTube EuclideanDimension.four 2).Nonempty :=
  wightmanBackwardTube_nonempty EuclideanDimension.four 2

/-- Dimension one also has the strict time tube; it does not require a spatial direction. -/
theorem one_dimensional_tube_nonempty :
    (wightmanBackwardTube EuclideanDimension.one 1).Nonempty :=
  wightmanBackwardTube_nonempty EuclideanDimension.one 1

/-- The strict tube rejects the zero complex point at positive arity. -/
theorem strict_tube_rejects_zero (d : EuclideanDimension) :
    (0 : Fin 1 → ComplexifiedSpacetime d) ∉ wightmanBackwardTube d 1 :=
  zero_not_mem_wightmanBackwardTube d (by decide)

/-- A positive-imaginary time point has the wrong sign and is rejected. -/
theorem positive_imaginary_time_rejected (d : EuclideanDimension) :
    (fun _ : Fin 1 => fun i : d.CoordinateIndex =>
      if i = d.timeIndex then Complex.I else 0) ∉ wightmanBackwardTube d 1 := by
  intro hwrong
  have htime := (hwrong 0).1
  simp [complexifiedSpacetimeImaginaryPart, EuclideanDimension.timeIndex] at htime
  norm_num at htime

/-- The retained negative-imaginary standard point has the exact source-facing sign. -/
theorem negative_imaginary_standard_point_accepted (d : EuclideanDimension) :
    standardWightmanBackwardTubePoint d 1 ∈ wightmanBackwardTube d 1 :=
  standardWightmanBackwardTubePoint_mem d 1

end YangMills.Minkowski.WightmanTubeGeometry.Probes
