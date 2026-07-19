/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalClustering

/-!
# Hostile probes for exact-source clustering

These probes lock the exact source pair, unrestricted reflection/translation/convolution, universal
nonzero spatial directions, strict restriction, and positive-arity content. They construct no
clustering Schwinger family or reconstruction.
-/

namespace YangMills.OSOrderedFourDimensionalClustering.Probes

open YangMills

/-- Four-dimensional clustering directions are inhabited concretely, so universal quantification is
not vacuous. -/
example : Nonempty (EuclideanUnitSpatialDirection EuclideanDimension.four) :=
  ⟨fourDimensionalCanonicalSpatialDirection⟩

/-- No accepted clustering direction is the zero spacetime vector. -/
theorem zero_direction_blocked :
    ¬ ∃ v : EuclideanUnitSpatialDirection EuclideanDimension.four, v.vector = 0 := by
  rintro ⟨v, hv⟩
  exact v.vector_ne_zero hv

/-- The connected expression uses the exact unrestricted source operations and factorization term. -/
example (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) (scale : ℝ) :
    osSourceFourDimensionalClusteringExpression family v f g scale =
      finiteSequenceSchwingerEvaluation family
          (finiteSchwartzSequenceConvolution EuclideanDimension.four
            (finiteSchwartzSequenceReflectedStar EuclideanDimension.four
              f.toFiniteSchwartzSequence)
            (translateScalarFiniteSchwartzSequenceAlongSpatialRay
              EuclideanDimension.four v scale g.toFiniteSchwartzSequence)) -
        finiteSequenceSchwingerEvaluation family
            (finiteSchwartzSequenceReflectedStar EuclideanDimension.four
              f.toFiniteSchwartzSequence) *
          finiteSequenceSchwingerEvaluation family g.toFiniteSchwartzSequence :=
  rfl

/-- The explicit positive-arity source bump survives in the untranslated factor. -/
theorem source_bump_factor_nonzero :
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence.toFiniteSchwartzSequence.component 1 ≠
      0 := by
  change positiveTimeBumpSchwartz EuclideanDimension.four ≠ 0
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

/-- Source `(E4)` supplies the canonical-direction limit for every exact source pair. -/
example {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (clustering : OSSourceFourDimensionalClustering family)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Filter.Tendsto
      (fun scale : ℝ => osSourceFourDimensionalClusteringExpression family
        fourDimensionalCanonicalSpatialDirection f g scale)
      Filter.atTop (nhds 0) :=
  clustering fourDimensionalCanonicalSpatialDirection f g

/-- Restricting both exact source inputs recovers the old strict expression exactly. -/
example (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four)
    (scale : ℝ) :
    osSourceFourDimensionalClusteringExpression family v
        f.toFourDimensionalOSSourceSequence g.toFourDimensionalOSSourceSequence scale =
      mathlibStrictScalarClusteringExpression family v f g scale :=
  osSourceFourDimensionalClusteringExpression_ofStrict family v f g scale

/-- Exact source clustering implies every strict-direction predicate in the valid direction. -/
example {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (clustering : OSSourceFourDimensionalClustering family)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four) :
    MathlibStrictScalarClusteringAlongDirection family v :=
  clustering.toMathlibStrictAlongDirection v

end YangMills.OSOrderedFourDimensionalClustering.Probes
