/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalVillainAction
import YangMills.Foundation.DimensionsProbes

/-!
# Probes for Driver's Villain action
-/

namespace YangMills.Dimensions.TwoDimensionalVillainAction.Probes

open MeasureTheory Set
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    (heat : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)

/-- The source parameter is literally `ε²`, not a fresh time assignment. -/
theorem exact_spacing_square (spacing : PositiveLatticeSpacing) :
    twoDimensionalVillainTime spacing = spacing.1 ^ 2 :=
  rfl

/-- The real action is definitionally the unchanged smooth heat-density representative at `ε²`. -/
theorem exact_real_heat_density (spacing : PositiveLatticeSpacing) (g : G) :
    twoDimensionalVillainAction heat kernel spacing g =
      heat.densityReal (spacing.1 ^ 2) g :=
  rfl

/-- The same action has the exact original `ENNReal` semigroup density, not a disconnected kernel. -/
theorem exact_selected_density_bridge (spacing : PositiveLatticeSpacing) (g : G) :
    ENNReal.ofReal (twoDimensionalVillainAction heat kernel spacing g) =
      law.selectedAreaDensity (spacing.1 ^ 2) g :=
  action_toENNReal heat kernel spacing g

/-- The inherited Driver action contract is continuous, strictly positive, central, inversion
symmetric, and normalized as a real Haar integral. -/
theorem exact_action_contract (spacing : PositiveLatticeSpacing) :
    Continuous (twoDimensionalVillainAction heat kernel spacing) ∧
      (∀ g : G, 0 < twoDimensionalVillainAction heat kernel spacing g) ∧
      (∀ h g : G, twoDimensionalVillainAction heat kernel spacing (h * g * h⁻¹) =
        twoDimensionalVillainAction heat kernel spacing g) ∧
      (∀ g : G, twoDimensionalVillainAction heat kernel spacing g⁻¹ =
        twoDimensionalVillainAction heat kernel spacing g) ∧
      (∫ g, twoDimensionalVillainAction heat kernel spacing g
        ∂normalizedCompactHaarMeasure G) = 1 :=
  ⟨action_continuous heat kernel spacing, action_pos heat kernel spacing,
    action_central heat kernel spacing, action_inv heat kernel spacing,
    action_integral_normalized heat kernel spacing⟩

/-- The Definition 4.7 Laplacian and exact `1/2` heat equation are part of the required chain. -/
theorem exact_heat_equation (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => heat.densityReal s g)
      ((1 / 2 : ℝ) * laplacian.laplacian (heat.smoothDensityAt t ht) g) t :=
  hasDerivAt_heatDensity heat t ht g

/-- The designated `exp(tΔ/2)` semigroup is literally convolution by the same real density. -/
theorem exact_operator_kernel_formula
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    kernel.heatOperator t f g =
      ∫ h, heat.densityReal t (h⁻¹ * g) * f h ∂normalizedCompactHaarMeasure G :=
  kernel.heatOperator_eq_kernelIntegral t ht f g

/-- The semigroup law normalizes the exact real-to-`ENNReal` plaquette density. -/
theorem exact_normalized_plaquette (spacing : PositiveLatticeSpacing) :
    twoDimensionalVillainPlaquetteMeasure heat kernel spacing univ = 1 ∧
      twoDimensionalVillainPlaquetteMeasure heat kernel spacing ≠ 0 :=
  ⟨plaquetteMeasure_univ heat kernel spacing, plaquetteMeasure_ne_zero heat kernel spacing⟩

/-- A zero plaquette measure is incompatible with exact semigroup normalization. -/
theorem zero_plaquette_blocked
    (spacing : PositiveLatticeSpacing)
    (claimed : twoDimensionalVillainPlaquetteMeasure heat kernel spacing = 0) : False :=
  (plaquetteMeasure_ne_zero heat kernel spacing) claimed

/-- A two-dimensional Villain plaquette action is not a four-dimensional continuum endpoint. -/
theorem villain_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalVillainAction.Probes
