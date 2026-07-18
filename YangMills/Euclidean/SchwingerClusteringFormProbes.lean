/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerClusteringForm
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for the strict-domain clustering form

The probes force source ordering, an explicit four-dimensional direction, the nonzero bump pair,
scale-dependent translated support, and rejection of a fake constant nonzero connected expression.
No clustering family is constructed.
-/

namespace YangMills.Euclidean.SchwingerClusteringForm.Probes

/-- The connected expression has the exact order `(Θ f*) × translated(g)` and subtracts the product
of separate reflected and untranslated evaluations. -/
theorem exact_clustering_expression
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (v : EuclideanUnitSpatialDirection d)
    (f g : MathlibStrictPositiveTimeTestSequence d) (scale : ℝ) :
    mathlibStrictScalarClusteringExpression family v f g scale =
      finiteSequenceSchwingerEvaluation family
          (finiteSchwartzSequenceConvolution d
            (finiteSchwartzSequenceReflectedStar d f.toFiniteSchwartzSequence)
            (translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale
              g.toFiniteSchwartzSequence)) -
        finiteSequenceSchwingerEvaluation family
            (finiteSchwartzSequenceReflectedStar d f.toFiniteSchwartzSequence) *
          finiteSequenceSchwingerEvaluation family g.toFiniteSchwartzSequence :=
  rfl

/-- The four-dimensional clustering form has an explicit, nonzero direction parameter. -/
noncomputable def explicit_four_dimensional_clustering_direction :
    EuclideanUnitSpatialDirection EuclideanDimension.four :=
  fourDimensionalCanonicalSpatialDirection

/-- The explicit clustering direction is genuinely nonzero. -/
theorem explicit_clustering_direction_ne_zero :
    explicit_four_dimensional_clustering_direction.vector ≠ 0 :=
  explicit_four_dimensional_clustering_direction.vector_ne_zero

/-- The translated second cluster retains exact support at every ray scale. -/
theorem translated_second_cluster_exact_support
    {d : EuclideanDimension} (v : EuclideanUnitSpatialDirection d)
    (g : MathlibStrictPositiveTimeTestSequence d) (scale : ℝ) :
    (mathlibStrictSpatialRayTranslatedSequence v scale g).support =
      g.toFiniteSchwartzSequence.support :=
  rfl

/-- The nonzero bump's arity-one component cannot disappear from the translated second cluster. -/
theorem translated_bump_cluster_one_mem_support
    {d : EuclideanDimension} (v : EuclideanUnitSpatialDirection d) (scale : ℝ) :
    1 ∈ (mathlibStrictSpatialRayTranslatedSequence v scale
      (singletonPositiveTimeBumpSequence d)).support := by
  rw [translated_second_cluster_exact_support]
  rw [_root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.forgotten_singleton_bump_support]
  simp

/-- Candidate clustering specializes to the explicit nonzero bump pair. -/
theorem candidate_forces_bump_pair_limit
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {v : EuclideanUnitSpatialDirection d}
    (h : MathlibStrictScalarClusteringAlongDirection family v) :
    Filter.Tendsto (fun scale : ℝ =>
      mathlibStrictScalarClusteringExpression family v
        (singletonPositiveTimeBumpSequence d)
        (singletonPositiveTimeBumpSequence d) scale)
      Filter.atTop (nhds 0) :=
  h (singletonPositiveTimeBumpSequence d) (singletonPositiveTimeBumpSequence d)

/-- A fake clustering form that stays equal to one along the whole ray contradicts the required
zero limit. -/
theorem constant_nonzero_bump_clustering_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {v : EuclideanUnitSpatialDirection d}
    (h : MathlibStrictScalarClusteringAlongDirection family v)
    (hconstant : ∀ scale : ℝ,
      mathlibStrictScalarClusteringExpression family v
        (singletonPositiveTimeBumpSequence d)
        (singletonPositiveTimeBumpSequence d) scale = 1) : False := by
  have hzero := candidate_forces_bump_pair_limit h
  have hone : Filter.Tendsto (fun scale : ℝ =>
      mathlibStrictScalarClusteringExpression family v
        (singletonPositiveTimeBumpSequence d)
        (singletonPositiveTimeBumpSequence d) scale)
      Filter.atTop (nhds 1) := by
    apply Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun scale => (hconstant scale).symm))
    exact tendsto_const_nhds
  have h01 : (0 : ℂ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at h01

/-- The clustering ray used by the form genuinely escapes to infinity. -/
theorem clustering_direction_escapes
    {d : EuclideanDimension} (v : EuclideanUnitSpatialDirection d) :
    Filter.Tendsto (fun scale : ℝ => ‖euclideanSpatialRayDisplacement d v scale‖)
      Filter.atTop Filter.atTop :=
  tendsto_norm_euclideanSpatialRayDisplacement_atTop d v

end YangMills.Euclidean.SchwingerClusteringForm.Probes
