/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Minkowski.MinkowskiBilinearForm

/-!
# Hostile probes for the mostly-minus Minkowski bilinear form
-/

namespace YangMills
namespace Minkowski
namespace MinkowskiBilinearForm
namespace Probes

/-- The time basis has positive unit self-pairing. -/
theorem exact_time_sign (d : EuclideanDimension) :
    minkowskiBilinearForm d (d.basisVector d.timeIndex)
      (d.basisVector d.timeIndex) = 1 := by
  rw [minkowskiBilinearForm_self]
  exact d.minkowskiQuadraticForm_time_basisVector

/-- Every actual spatial basis vector has negative unit self-pairing. -/
theorem exact_spatial_sign (d : EuclideanDimension)
    (i : Fin d.spatialDimension) :
    minkowskiBilinearForm d (d.basisVector (d.spatialIndexSucc i))
      (d.basisVector (d.spatialIndexSucc i)) = -1 := by
  rw [minkowskiBilinearForm_self]
  exact d.minkowskiQuadraticForm_spatial_basisVector i

/-- The exact time coordinate is recovered by pairing with the time basis. -/
theorem exact_time_coordinate (d : EuclideanDimension) (x : d.CoordinateVector) :
    minkowskiBilinearForm d (d.basisVector d.timeIndex) x = x d.timeIndex :=
  minkowskiBilinearForm_timeBasis_left d x

/-- Hostile probe: zero time coordinate cannot have positive Minkowski norm. -/
theorem positive_norm_blocks_zero_time
    (d : EuclideanDimension) {x : d.CoordinateVector}
    (hpositive : 0 < d.minkowskiQuadraticForm x) :
    x d.timeIndex ≠ 0 := by
  intro hzero
  exact (not_lt_of_ge (minkowskiQuadraticForm_nonpos_of_time_eq_zero d hzero)) hpositive

/-- Quadratic-form preservation cannot be paired with a disconnected bilinear action. -/
theorem exact_polarized_preservation
    (d : EuclideanDimension)
    (linear : d.CoordinateVector →ₗ[ℝ] d.CoordinateVector)
    (preservesQuadratic : ∀ x,
      d.minkowskiQuadraticForm (linear x) = d.minkowskiQuadraticForm x)
    (x y : d.CoordinateVector) :
    minkowskiBilinearForm d (linear x) (linear y) =
      minkowskiBilinearForm d x y :=
  minkowskiBilinearForm_map_eq_of_quadratic_preserving d linear preservesQuadratic x y

end Probes
end MinkowskiBilinearForm
end Minkowski
end YangMills
