/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalEuclideanCurrentStrength

/-!
# Hostile probes for the exact-source Euclidean current-strength package

These projections ensure ambient-extension OS-II growth and `(E1)`–`(E4)` use one exact family,
while the derived carrier-exact growth, source positivity, and source clustering reach their exact
domains. They construct no family or reconstruction.
-/

namespace YangMills.OSOrderedFourDimensionalEuclideanCurrentStrength.Probes

open YangMills

variable
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (data : OSSourceFourDimensionalEuclideanCurrentStrengthData family)

/-- Ambient-extension OS-II growth remains indexed by the exact same family. -/
example : OSIIAmbientExtensionLinearGrowthData family :=
  data.linearGrowth

/-- Carrier-exact OS-II growth is derived on the exact coincidence-flat restriction. -/
noncomputable example :
    OSIICarrierExactLinearGrowthData family.toOSIICoincidenceFlatFamily :=
  data.carrierExactLinearGrowth

/-- Covariance remains indexed by the exact same family. -/
example : ScalarSchwingerEuclideanCovariance family :=
  data.covariance

/-- Source positivity remains indexed by the exact same family. -/
example : OSSourceFourDimensionalReflectionPositivity family :=
  data.reflectionPositivity

/-- Symmetry remains indexed by the exact same family. -/
example : ScalarSchwingerPermutationSymmetry family :=
  data.symmetry

/-- Source clustering remains indexed by the exact same family. -/
example : OSSourceFourDimensionalClustering family :=
  data.clustering

/-- Positivity reaches every exact derivative-vanishing source sequence. -/
example (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    IsNonnegativeComplexReal
      (osSourceFourDimensionalReflectionPositivityExpression family f) :=
  data.reflectionPositivity_apply f

/-- Clustering reaches every exact source pair and every normalized direction. -/
example (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Filter.Tendsto
      (fun scale : ℝ => osSourceFourDimensionalClusteringExpression family v f g scale)
      Filter.atTop (nhds 0) :=
  data.clustering_apply v f g

/-- The exact source package cannot silently use only the zero-arity component. -/
theorem positive_arity_source_test_nonzero :
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence.toFiniteSchwartzSequence.component 1 ≠
      0 := by
  change positiveTimeBumpSchwartz EuclideanDimension.four ≠ 0
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

end YangMills.OSOrderedFourDimensionalEuclideanCurrentStrength.Probes
