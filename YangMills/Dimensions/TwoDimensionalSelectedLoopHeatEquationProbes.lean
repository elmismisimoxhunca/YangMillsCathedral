/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatEquation

/-!
# Hostile probes for the selected-loop heat equation

The probes expose the exact compact-simple group index, positive smooth real representative,
pointwise bridge to the unchanged `ENNReal` density, Driver's `+1/2` pairing-Laplacian derivative,
and inherited central/inversion symmetry. They reject a disconnected density and changed derivative.
No density, heat kernel, Brownian motion, or theory is constructed.
-/

namespace YangMills.Dimensions.TwoDimensionalSelectedLoopHeatEquation.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

noncomputable section

variable
    {E G Gauge Sample Connection : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group Gauge] [MeasurableSpace Sample]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}

/-- The heat-equation surface is indexed by the exact compact-connected-simple project group. -/
theorem exact_compact_simple_group
    (_data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian) :
    Geometry.CompactSimpleGaugeGroupData G E :=
  gaugeGroup

/-- The positive-time real representative is spatially smooth on the exact group manifold. -/
theorem exact_spatial_smoothness
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) :
    ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞ (data.densityReal t) :=
  data.densityReal_spatialSmooth t ht

/-- The real representative is tied pointwise to the unchanged semigroup density family. -/
theorem exact_same_density_bridge
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    ENNReal.ofReal (data.densityReal t g) = law.selectedAreaDensity t g :=
  data.densityReal_toENNReal t ht g

/-- Driver's sign and factor are exactly `+1/2` times the same pairing Laplacian. -/
theorem exact_heat_equation
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => data.densityReal s g)
      ((1 / 2 : ℝ) * laplacian.laplacian (data.smoothDensityAt t ht) g) t :=
  data.hasDerivAt_densityReal t ht g

/-- A changed time derivative cannot replace the exact `+1/2` Laplacian value. -/
theorem changed_heat_derivative_blocked
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) (wrong : ℝ)
    (different : wrong ≠
      (1 / 2 : ℝ) * laplacian.laplacian (data.smoothDensityAt t ht) g)
    (claimed : HasDerivAt (fun s => data.densityReal s g) wrong t) : False := by
  apply different
  exact claimed.unique (data.hasDerivAt_densityReal t ht g)

/-- A disconnected `ENNReal` value is rejected by the exact pointwise bridge. -/
theorem changed_density_bridge_blocked
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) (wrong : ENNReal)
    (different : wrong ≠ law.selectedAreaDensity t g)
    (claimed : ENNReal.ofReal (data.densityReal t g) = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.densityReal_toENNReal t ht g

/-- Strict source positivity blocks a zero positive-time representative. -/
theorem zero_real_density_blocked
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G)
    (claimed : data.densityReal t g = 0) : False :=
  data.densityReal_ne_zero t ht g claimed

/-- Centrality descends from the exact unchanged `ENNReal` density. -/
theorem exact_real_density_central
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (h g : G) :
    data.densityReal t (h * g * h⁻¹) = data.densityReal t g :=
  data.densityReal_central t ht h g

/-- Inversion symmetry descends from the exact unchanged `ENNReal` density. -/
theorem exact_real_density_inv
    (data : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    data.densityReal t g⁻¹ = data.densityReal t g :=
  data.densityReal_inv t ht g

/-- This lower-dimensional heat-equation surface cannot change the Clay endpoint index. -/
theorem heat_equation_cannot_be_four :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSelectedLoopHeatEquation.Probes
