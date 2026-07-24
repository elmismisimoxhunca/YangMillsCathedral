/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralHeatOperatorLinear

namespace YangMills
namespace Dimensions

open Filter MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact positive-time linearity probe. -/
theorem exact_positiveHeatOperator_linearity
    (t : ℝ) (ht : 0 < t) (c : ℝ) (f h : C(G, ℝ)) :
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht (c • f + h) =
      c • twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f +
        twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht h := by
  rw [map_add, map_smul]

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact totalization probe: the excluded zero-time branch is the zero linear map. -/
theorem exact_heatDifferenceQuotientLinearMap_zero :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge 0 = 0 :=
  twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_zero bridge

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile zero-branch probe: no changed linear map can replace the designated totalization. -/
theorem changed_heatDifferenceQuotientLinearMap_zero_blocked
    (changed : C(G, ℝ) →ₗ[ℝ] C(G, ℝ)) (changed_ne_zero : changed ≠ 0)
    (claimed : twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge 0 = changed) :
    False :=
  changed_ne_zero (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_zero bridge))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact pointwise quotient probe. -/
theorem exact_heatDifferenceQuotientLinearMap
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f g =
      (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g - f g) /
        (t : ℝ) :=
  twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply_point bridge t ht f g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile probe: the positive heat linear map cannot be changed while preserving its designated
operator value. -/
theorem changed_positiveHeatOperatorLinearMap_blocked
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      bridge.spectralHeatKernel.kernelOperator.heatOperator t f)
    (claimed : twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f = changed) :
    False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_apply bridge t ht f))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile quotient probe: a changed scalar point value contradicts the exact bundled quotient. -/
theorem changed_heatDifferenceQuotientLinearMap_point_blocked
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g - f g) / (t : ℝ))
    (claimed : twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f g = changed) :
    False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply_point bridge t ht f g))

end

end Dimensions
end YangMills
