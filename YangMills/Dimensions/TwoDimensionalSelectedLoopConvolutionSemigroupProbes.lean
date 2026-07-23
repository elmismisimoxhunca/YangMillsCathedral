/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup

/-!
# Hostile probes for the selected-loop convolution semigroup

The probes expose all-positive-time normalization, the exact `x⁻¹ * g` orientation, weak convergence
to the identity, the selected-area half split, and rejection of zero or changed density laws. They
do not call the family a heat kernel or add metric/PDE/Brownian semantics.
-/

namespace YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup.Probes

open MeasureTheory Filter
open YangMills.Mathematics

noncomputable section

variable {G Gauge Sample Connection : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [Group Gauge] [MeasurableSpace Sample]
  {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
  {law : TwoDimensionalSelectedLoopHaarDensityLawData base}

/-- The selected-loop certificate forgets exactly to the reusable source-neutral semigroup. -/
theorem exact_sourceNeutral_semigroup
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law) :
    NormalizedCompactHaarDensitySemigroupData law.selectedAreaDensity :=
  semigroup.toNormalizedCompactHaarDensitySemigroupData

/-- Every positive-time density is normalized against the exact canonical Haar probability. -/
theorem exact_positive_time_normalization
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (t : ℝ) (ht : 0 < t) :
    ∫⁻ g, law.selectedAreaDensity t g ∂normalizedCompactHaarMeasure G = 1 :=
  semigroup.density_lintegral_normalized t ht

/-- The primitive addition law retains the Driver/Sengupta `x⁻¹ * g` orientation. -/
theorem exact_driver_sengupta_convolution_orientation
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (g : G) :
    law.selectedAreaDensity (s + t) g =
      ∫⁻ x, law.selectedAreaDensity s x *
        law.selectedAreaDensity t (x⁻¹ * g)
        ∂normalizedCompactHaarMeasure G := by
  rw [semigroup.density_add s t hs ht g]
  rfl

/-- A wrong convolution value cannot replace the exact same-family addition law. -/
theorem wrong_convolution_value_blocked
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (g : G) (wrong : ENNReal)
    (different : wrong ≠ normalizedCompactHaarDensityConvolution G
      (law.selectedAreaDensity s) (law.selectedAreaDensity t) g)
    (claimed : law.selectedAreaDensity (s + t) g = wrong) : False := by
  apply different
  rw [← claimed]
  exact semigroup.density_add s t hs ht g

/-- A syntactically reversed primitive convolution cannot be substituted whenever the two
expressions are observably different. Centrality may prove equality in special cases, so the
probe deliberately requires the distinction premise. -/
theorem reversed_primitive_orientation_blocked_when_distinct
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (g : G)
    (different :
      (∫⁻ x, law.selectedAreaDensity s x *
        law.selectedAreaDensity t (g * x⁻¹)
        ∂normalizedCompactHaarMeasure G) ≠
      normalizedCompactHaarDensityConvolution G
        (law.selectedAreaDensity s) (law.selectedAreaDensity t) g)
    (claimed : law.selectedAreaDensity (s + t) g =
      ∫⁻ x, law.selectedAreaDensity s x *
        law.selectedAreaDensity t (g * x⁻¹)
        ∂normalizedCompactHaarMeasure G) : False := by
  apply different
  rw [← claimed]
  exact semigroup.density_add s t hs ht g

/-- Weak convergence is to evaluation at the group identity, not to Haar averaging. -/
theorem exact_weak_identity_limit
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (f : C(G, ℂ)) :
    Tendsto
      (fun t : ℝ => ∫ g, f g
        ∂((normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1)) :=
  semigroup.weak_tendsto_identity f

/-- The selected positive area has an exact source-oriented two-half subdivision identity. -/
theorem exact_selected_area_half_split
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law) (g : G) :
    law.selectedAreaDensity law.enclosedArea g =
      normalizedCompactHaarDensityConvolution G
        (law.selectedAreaDensity
          (TwoDimensionalSelectedLoopConvolutionSemigroupData.selectedHalfArea (law := law)))
        (law.selectedAreaDensity
          (TwoDimensionalSelectedLoopConvolutionSemigroupData.selectedHalfArea (law := law))) g :=
  semigroup.selectedArea_half_split g

/-- A zero positive-time density contradicts exact normalization. -/
theorem zero_positive_time_density_blocked
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (t : ℝ) (ht : 0 < t)
    (claimed : law.selectedAreaDensity t = 0) : False :=
  semigroup.positiveTimeDensity_ne_zero t ht claimed

/-- This lower-dimensional semigroup cannot change the Clay endpoint index. -/
theorem convolution_semigroup_cannot_be_four :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup.Probes
