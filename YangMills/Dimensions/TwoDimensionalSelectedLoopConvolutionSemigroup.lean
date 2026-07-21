/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopHaarDensityLaw
import YangMills.Mathematics.NormalizedCompactHaarConvolution

/-!
# Positive-time convolution semigroup for the selected two-dimensional loop density

Driver's semigroup kernel uses `Q_t(h⁻¹g)`. Sengupta explicitly composes area-clocked densities by
`∫ Q_s(x) Q_t(x⁻¹z) dx`, and Witten's equation (2.48) uses the same glued-edge orientation.

This module strengthens one exact `TwoDimensionalSelectedLoopHaarDensityLawData`; it does not choose
a second density family. Every positive-time density is normalized, density addition is the exact
normalized-Haar convolution, and weak convergence to the identity is required against every
continuous complex test function. Whenever continuous functions distinguish the identity—as they
do on the intended Hausdorff compact Lie group—the latter prevents a time-constant Haar density
from serving as a fake approximate identity.

This remains a convolution-semigroup acceptance certificate, not a heat-kernel certificate: no
invariant metric, Laplacian, Brownian generator, heat equation, or smooth real representative is
supplied or constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory Filter
open YangMills.Mathematics

noncomputable section

/-- Exact normalized positive-time convolution-semigroup requirements for the unchanged selected
loop density family. -/
structure TwoDimensionalSelectedLoopConvolutionSemigroupData
    {G Gauge Sample Connection : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) where
  /-- Every positive-time density is normalized against the same canonical Haar probability. -/
  density_lintegral_normalized : ∀ t, 0 < t →
    ∫⁻ g, law.selectedAreaDensity t g ∂normalizedCompactHaarMeasure G = 1
  /-- Exact Driver/Sengupta orientation of the density addition law. -/
  density_add : ∀ s t, 0 < s → 0 < t → ∀ g,
    law.selectedAreaDensity (s + t) g =
      normalizedCompactHaarDensityConvolution G
        (law.selectedAreaDensity s) (law.selectedAreaDensity t) g
  /-- Weak approximate-identity behavior at positive time zero. This rules out the constant Haar
  idempotent whenever continuous functions distinguish the identity. -/
  weak_tendsto_identity : ∀ f : C(G, ℂ),
    Tendsto
      (fun t : ℝ => ∫ g, f g
        ∂((normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1))

namespace TwoDimensionalSelectedLoopConvolutionSemigroupData

variable {G Gauge Sample Connection : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [Group Gauge] [MeasurableSpace Sample]
  {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
  {law : TwoDimensionalSelectedLoopHaarDensityLawData base}

/-- Half of the exact selected positive area. -/
noncomputable def selectedHalfArea : ℝ :=
  law.enclosedArea / 2

/-- The selected half-area remains strictly positive. -/
theorem selectedHalfArea_pos : 0 < selectedHalfArea (law := law) := by
  exact half_pos law.enclosedArea_pos

/-- Two selected half-areas add back to the exact original area. -/
theorem selectedHalfArea_add_self :
    selectedHalfArea (law := law) + selectedHalfArea (law := law) = law.enclosedArea := by
  simp [selectedHalfArea]

/-- Every positive-time density measure is a probability measure, derived from the density
normalization and not accepted as a second disconnected field. -/
theorem densityMeasure_univ_of_pos
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (t : ℝ) (ht : 0 < t) :
    ((normalizedCompactHaarMeasure G).withDensity
      (law.selectedAreaDensity t)) Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using semigroup.density_lintegral_normalized t ht

/-- The selected positive-area density splits exactly into two same-family half-area factors with
the source-facing `x⁻¹ * g` convolution orientation. -/
theorem selectedArea_half_split
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law) (g : G) :
    law.selectedAreaDensity law.enclosedArea g =
      normalizedCompactHaarDensityConvolution G
        (law.selectedAreaDensity (selectedHalfArea (law := law)))
        (law.selectedAreaDensity (selectedHalfArea (law := law))) g := by
  rw [← selectedHalfArea_add_self (law := law)]
  exact semigroup.density_add _ _ selectedHalfArea_pos selectedHalfArea_pos g

/-- No positive-time density in the certified family can be the zero function. -/
theorem positiveTimeDensity_ne_zero
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (t : ℝ) (ht : 0 < t) : law.selectedAreaDensity t ≠ 0 := by
  intro zero_density
  have normalized := semigroup.density_lintegral_normalized t ht
  rw [zero_density] at normalized
  simp at normalized

end TwoDimensionalSelectedLoopConvolutionSemigroupData

end

end YangMills.Dimensions
