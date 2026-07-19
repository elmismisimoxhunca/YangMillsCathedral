/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalReflectionPositivity
import YangMills.Euclidean.SchwingerClusteringForm

/-!
# Clustering on the exact four-dimensional OS-I source carrier

OS-I `(E4)` requires connected Schwinger correlations to vanish when one source sequence is
translated to spatial infinity. This module states that limit for every normalized nonzero spatial
direction and every pair of exact derivative-vanishing source sequences.

The source sequences are forgotten componentwise into the unrestricted finite Schwartz algebra
before reflection, translation, convolution, and evaluation. This is exact algebraic source-carrier
`(E4)` data. OS-II growth and corrected reconstruction remain distinct obligations, and no
clustering Schwinger family is constructed.
-/

namespace YangMills

noncomputable section

/-- Exact unrestricted reflected-star sequence of an OS-I source sequence. -/
noncomputable def osSourceFourDimensionalReflectedStarSequence
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    ScalarFiniteSchwartzSequence EuclideanDimension.four :=
  finiteSchwartzSequenceReflectedStar EuclideanDimension.four
    f.toFiniteSchwartzSequence

/-- Exact unrestricted source sequence translated along a normalized spatial ray. -/
noncomputable def osSourceFourDimensionalSpatialRayTranslatedSequence
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four) (scale : ℝ)
    (g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    ScalarFiniteSchwartzSequence EuclideanDimension.four :=
  translateScalarFiniteSchwartzSequenceAlongSpatialRay EuclideanDimension.four v scale
    g.toFiniteSchwartzSequence

/-- Exact connected source-carrier clustering expression at one spatial-ray scale. -/
noncomputable def osSourceFourDimensionalClusteringExpression
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) (scale : ℝ) : ℂ :=
  finiteSequenceSchwingerEvaluation family
      (finiteSchwartzSequenceConvolution EuclideanDimension.four
        (osSourceFourDimensionalReflectedStarSequence f)
        (osSourceFourDimensionalSpatialRayTranslatedSequence v scale g)) -
    finiteSequenceSchwingerEvaluation family
        (osSourceFourDimensionalReflectedStarSequence f) *
      finiteSequenceSchwingerEvaluation family g.toFiniteSchwartzSequence

/-- OS-I `(E4)` on the exact four-dimensional source carrier.

Quantifying over normalized nonzero spatial directions prevents a disconnected or zero translation
witness. -/
def OSSourceFourDimensionalClustering
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four) : Prop :=
  ∀ (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence),
    Filter.Tendsto
      (fun scale : ℝ => osSourceFourDimensionalClusteringExpression family v f g scale)
      Filter.atTop (nhds 0)

/-- Exact source clustering exposes the limit for every direction and source pair. -/
theorem OSSourceFourDimensionalClustering.apply
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (clustering : OSSourceFourDimensionalClustering family)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Filter.Tendsto
      (fun scale : ℝ => osSourceFourDimensionalClusteringExpression family v f g scale)
      Filter.atTop (nhds 0) :=
  clustering v f g

/-- The exact source expression restricts definitionally to the earlier strict-domain expression. -/
theorem osSourceFourDimensionalClusteringExpression_ofStrict
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four)
    (f g : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four)
    (scale : ℝ) :
    osSourceFourDimensionalClusteringExpression family v
        f.toFourDimensionalOSSourceSequence g.toFourDimensionalOSSourceSequence scale =
      mathlibStrictScalarClusteringExpression family v f g scale := by
  unfold osSourceFourDimensionalClusteringExpression
    osSourceFourDimensionalReflectedStarSequence
    osSourceFourDimensionalSpatialRayTranslatedSequence
    mathlibStrictScalarClusteringExpression
    mathlibStrictReflectedStarSequence
    mathlibStrictSpatialRayTranslatedSequence
  rw [OSPositiveTimeOrderedFourDimensionalTestSequence.toFiniteSchwartzSequence_ofStrict,
    OSPositiveTimeOrderedFourDimensionalTestSequence.toFiniteSchwartzSequence_ofStrict]

/-- Source-carrier clustering implies strict-subdomain clustering along every supplied direction.
The converse is not claimed. -/
theorem OSSourceFourDimensionalClustering.toMathlibStrictAlongDirection
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (clustering : OSSourceFourDimensionalClustering family)
    (v : EuclideanUnitSpatialDirection EuclideanDimension.four) :
    MathlibStrictScalarClusteringAlongDirection family v := by
  intro f g
  have sourceLimit := clustering v
    f.toFourDimensionalOSSourceSequence g.toFourDimensionalOSSourceSequence
  simpa only [osSourceFourDimensionalClusteringExpression_ofStrict] using sourceLimit

end

end YangMills
