/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.ReverseWickRotationGeometry

/-!
# Hostile probes for reverse Wick-rotation geometry

The probes expose time-only complexification, reversed point order, strict Euclidean nonvacuity,
and exact backward-tube landing in dimensions one and four. No correlator continuation is asserted.
-/

namespace YangMills.Reconstruction.ReverseWickRotationGeometry.Probes

open Minkowski

/-- Wick rotation sends the reversed Euclidean time exactly to negative imaginary time. -/
theorem exact_reverse_wick_time
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d n) (j : Fin n) :
    reverseWickRotateEuclideanConfiguration d n x j (euclideanTimeCoordinate d) =
      -Complex.I * Complex.ofReal (x j.rev (euclideanTimeCoordinate d)) := by
  simp [reverseWickRotateEuclideanConfiguration]

/-- Spatial coordinates remain real under the bridge. -/
theorem exact_reverse_wick_spatial
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d n)
    (j : Fin n) (i : d.CoordinateIndex) (hi : i ≠ euclideanTimeCoordinate d) :
    reverseWickRotateEuclideanConfiguration d n x j i =
      Complex.ofReal (x j.rev i) := by
  simp [reverseWickRotateEuclideanConfiguration, hi]

/-- The explicit standard Euclidean configuration is strict and nonvacuous at every arity. -/
theorem exact_standard_strict_configuration
    (d : EuclideanDimension) (n : ℕ) :
    standardStrictEuclideanConfiguration d n ∈
      strictPositiveTimeOrderedConfigurationSet d n :=
  standardStrictEuclideanConfiguration_mem d n

/-- Four-dimensional three-point Euclidean data lands in the two-relative-coordinate tube. -/
theorem four_dimensional_standard_configuration_lands_in_tube :
    reverseWickRotatedRelativeCoordinates EuclideanDimension.four 2
      (standardStrictEuclideanConfiguration EuclideanDimension.four 3) ∈
      wightmanBackwardTube EuclideanDimension.four 2 :=
  reverseWickRotatedRelativeCoordinates_mem_backwardTube
    EuclideanDimension.four 2 _
    (standardStrictEuclideanConfiguration_mem EuclideanDimension.four 3)

/-- Dimension-one ordered Euclidean data lands in its genuine time tube. -/
theorem one_dimensional_standard_configuration_lands_in_tube :
    reverseWickRotatedRelativeCoordinates EuclideanDimension.one 1
      (standardStrictEuclideanConfiguration EuclideanDimension.one 2) ∈
      wightmanBackwardTube EuclideanDimension.one 1 :=
  reverseWickRotatedRelativeCoordinates_mem_backwardTube
    EuclideanDimension.one 1 _
    (standardStrictEuclideanConfiguration_mem EuclideanDimension.one 2)

/-- The negative imaginary part is the exact positive reversed time difference times the time basis. -/
theorem exact_negative_imaginary_difference
    (d : EuclideanDimension) (n : ℕ) (x : EuclideanNPointSpace d (n + 1))
    (j : Fin n) :
    -complexifiedSpacetimeImaginaryPart
      (reverseWickRotatedRelativeCoordinates d n x j) =
      (x j.castSucc.rev (euclideanTimeCoordinate d) -
        x j.succ.rev (euclideanTimeCoordinate d)) • d.basisVector d.timeIndex :=
  negative_imaginary_reverseWickRotatedRelativeCoordinates d n x j

/-- Omitting the point reversal gives the wrong sign even for the explicit strict two-point
configuration. -/
theorem unreversed_standard_configuration_rejected
    (d : EuclideanDimension) :
    unreversedWickRotatedRelativeCoordinates d 1
      (standardStrictEuclideanConfiguration d 2) ∉ wightmanBackwardTube d 1 :=
  unreversed_standard_twoPoint_not_mem_backwardTube d

end YangMills.Reconstruction.ReverseWickRotationGeometry.Probes
