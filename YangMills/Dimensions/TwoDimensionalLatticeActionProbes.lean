/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeAction

/-!
# Probes for Driver's common lattice-action contract
-/

namespace YangMills.Dimensions.TwoDimensionalLatticeActionData.Probes

open MeasureTheory
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
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}

/-- Packaging preserves the exact Villain action rather than selecting a replacement. -/
theorem exact_villain_action
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) (g : G) :
    (villain heat kernel spacing).action g =
      twoDimensionalVillainAction heat kernel spacing g :=
  rfl

omit [T2Space G] [SecondCountableTopology G] in
/-- Packaging preserves the exact Wilson action rather than selecting a replacement. -/
theorem exact_wilson_action
    {representation : FiniteDimensionalUnitaryRepresentationCharacterData G}
    (normalization : TwoDimensionalWilsonNormalizerData representation)
    (spacing : PositiveLatticeSpacing) (g : G) :
    (wilson normalization spacing).action g =
      twoDimensionalWilsonAction normalization spacing g :=
  rfl

omit [T2Space G] [SecondCountableTopology G] in
/-- The common carrier exposes every inherited Definition 7.1 obligation together. -/
theorem exact_common_contract (data : TwoDimensionalLatticeActionData G) :
    Continuous data.action ∧
      (∀ g, 0 < data.action g) ∧
      (∀ h g, data.action (h * g * h⁻¹) = data.action g) ∧
      (∀ g, data.action g⁻¹ = data.action g) ∧
      (∫ g, data.action g ∂normalizedCompactHaarMeasure G) = 1 :=
  ⟨data.action_continuous, data.action_pos, data.action_central, data.action_inv,
    data.action_integral_normalized⟩

omit [T2Space G] [SecondCountableTopology G] in
/-- The common contract is constructively nonempty without constructing a lattice field. -/
theorem constant_action_positive (g : G) :
    constantOne.action g = 1 ∧ 0 < constantOne.action g :=
  ⟨rfl, zero_lt_one⟩

omit [T2Space G] [SecondCountableTopology G] in
/-- The zero-action surrogate is rejected by strict positivity. -/
theorem zero_action_blocked
    (data : TwoDimensionalLatticeActionData G)
    (claimed : data.action = 0) : False :=
  data.action_ne_zero claimed

omit [T2Space G] [SecondCountableTopology G] in
/-- A falsely normalized action is rejected by the exact real Haar integral field. -/
theorem wrong_normalization_blocked
    (data : TwoDimensionalLatticeActionData G)
    (wrong : ∫ g, data.action g ∂normalizedCompactHaarMeasure G ≠ 1) : False :=
  wrong data.action_integral_normalized

end

end YangMills.Dimensions.TwoDimensionalLatticeActionData.Probes
