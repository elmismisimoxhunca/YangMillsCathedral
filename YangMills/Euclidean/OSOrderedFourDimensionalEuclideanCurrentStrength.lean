/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalClustering
import YangMills.Euclidean.SchwingerEuclideanCandidate

/-!
# Current-strength Euclidean axioms on the exact four-dimensional OS source carrier

This record assembles one normalized scalar Schwinger family with proper-Euclidean covariance
`(E1)`, permutation symmetry `(E3)`, and exact source-carrier positivity/clustering `(E2)/(E4)`.
It retains the project's concrete full-Schwartz fixed-order factorial estimate as preliminary
regularity data.

The record is explicitly `CurrentStrength`: the concrete Mathlib seminorm has not been identified
with OS-II's printed `|f|_{n,s}`, so this is not yet source-facing `(E0′)` and cannot feed a corrected
reconstruction theorem. No Schwinger family inhabitant is constructed.
-/

namespace YangMills

/-- Current-strength four-dimensional Euclidean axiom package on one exact source family. -/
structure OSSourceFourDimensionalEuclideanCurrentStrengthData
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four) where
  /-- Preliminary fixed-order factorial growth on full Mathlib Schwartz spaces. -/
  fixedOrderGrowth : MathlibFixedOrderFactorialGrowthData family
  /-- Proper-Euclidean covariance `(E1)` on the same family. -/
  covariance : ScalarSchwingerEuclideanCovariance family
  /-- Exact source-carrier reflection positivity `(E2)`. -/
  reflectionPositivity : OSSourceFourDimensionalReflectionPositivity family
  /-- Permutation symmetry `(E3)` on the same family. -/
  symmetry : ScalarSchwingerPermutationSymmetry family
  /-- Exact source-carrier clustering `(E4)` in every normalized spatial direction. -/
  clustering : OSSourceFourDimensionalClustering family

namespace OSSourceFourDimensionalEuclideanCurrentStrengthData

/-- Every source test has the exact nonnegative reflected-star Schwinger evaluation. -/
theorem reflectionPositivity_apply
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (data : OSSourceFourDimensionalEuclideanCurrentStrengthData family)
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    IsNonnegativeComplexReal
      (osSourceFourDimensionalReflectionPositivityExpression family f) :=
  data.reflectionPositivity f

/-- Every source pair clusters along every normalized nonzero spatial direction. -/
theorem clustering_apply
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (data : OSSourceFourDimensionalEuclideanCurrentStrengthData family)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Filter.Tendsto
      (fun scale : ℝ => osSourceFourDimensionalClusteringExpression family v f g scale)
      Filter.atTop (nhds 0) :=
  data.clustering v f g

/-- Restrict current source-carrier data to the earlier strict candidate along any exact direction. -/
def toMathlibStrictCandidate
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (data : OSSourceFourDimensionalEuclideanCurrentStrengthData family)
    (direction : EuclideanUnitSpatialDirection EuclideanDimension.four) :
    MathlibStrictScalarEuclideanCandidate family direction where
  fixedOrderGrowth := data.fixedOrderGrowth
  covariance := data.covariance
  symmetry := data.symmetry
  reflectionPositivity := data.reflectionPositivity.toMathlibStrict
  clustering := data.clustering.toMathlibStrictAlongDirection direction

end OSSourceFourDimensionalEuclideanCurrentStrengthData

end YangMills
