/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalClustering
import YangMills.Euclidean.OSIILinearGrowth

/-!
# Current-strength Euclidean axioms on the exact four-dimensional OS source carrier

This record assembles one normalized ambient tempered Schwinger family with carrier-exact OS-II
linear growth on its coincidence-flat restriction, proper-Euclidean covariance `(E1)`, source
positivity `(E2)`, permutation symmetry `(E3)`, and source clustering `(E4)`.

The record remains explicitly `CurrentStrength`: it requires extra ambient full-Schwartz extensions,
and no corrected reconstruction bridge has yet been stated. No Schwinger family inhabitant is
constructed.
-/

namespace YangMills

/-- Current-strength four-dimensional Euclidean axiom package on one exact source family. -/
structure OSSourceFourDimensionalEuclideanCurrentStrengthData
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four) where
  /-- Exact OS-II `(E0′)` on the coincidence-flat restriction, with this family's ambient tempered
  extensions retained as explicit strengthening data. -/
  linearGrowth : OSIIAmbientExtensionLinearGrowthData family
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

/-- The ambient growth requirement restricts canonically to carrier-exact OS-II `(E0′)` data. -/
noncomputable def carrierExactLinearGrowth
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (data : OSSourceFourDimensionalEuclideanCurrentStrengthData family) :
    OSIICarrierExactLinearGrowthData family.toOSIICoincidenceFlatFamily :=
  data.linearGrowth.toCarrierExact

end OSSourceFourDimensionalEuclideanCurrentStrengthData

end YangMills
