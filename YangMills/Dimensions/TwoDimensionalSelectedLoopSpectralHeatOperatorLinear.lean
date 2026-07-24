/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopStochasticGeneratorAtZero
import YangMills.Mathematics.LieGroupRightInvariantScalarDerivativeSmoothness
import YangMills.Mathematics.LinearMapGraphCoreGenerator

/-!
# Linear selected-loop spectral heat operators

The generated heat operator was originally stored as a function on `C(G, ℝ)`. Its exact spectral
probability-measure formula proves positive-time additivity and real homogeneity. This file bundles
that operator, and its positive right-hand difference quotient, as algebraic linear maps on
`C(G, ℝ)`.

No graph bound, graph density, or smooth-domain zero-time generator theorem is asserted here.
-/

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

/-- At positive time, the generated spectral heat operator is an algebraic real linear map on
continuous functions. -/
noncomputable def twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) : C(G, ℝ) →ₗ[ℝ] C(G, ℝ) where
  toFun := bridge.spectralHeatKernel.kernelOperator.heatOperator t
  map_add' f h := by
    let μ := unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t
    letI : IsFiniteMeasure μ := ⟨by
      rw [show μ Set.univ = 1 from unitaryMatrixDualCasimirHeatProbabilityMeasure_univ
        bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.casimirBridge
        bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.positivity ht]
      simp⟩
    ext g
    rw [bridge.generated_operator_eq_spectralMeasureIntegral t ht]
    simp only [ContinuousMap.coe_add, Pi.add_apply]
    rw [bridge.generated_operator_eq_spectralMeasureIntegral t ht,
      bridge.generated_operator_eq_spectralMeasureIntegral t ht, integral_add]
    · have hc : Continuous (fun x => f (g * x)) :=
        f.continuous.comp (continuous_const_mul g)
      simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
        (μ := unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t) isCompact_univ
    · have hc : Continuous (fun x => h (g * x)) :=
        h.continuous.comp (continuous_const_mul g)
      simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
        (μ := unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t) isCompact_univ
  map_smul' c f := by
    ext g
    rw [bridge.generated_operator_eq_spectralMeasureIntegral t ht]
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [bridge.generated_operator_eq_spectralMeasureIntegral t ht, integral_const_mul]

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_apply
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) :
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f =
      bridge.spectralHeatKernel.kernelOperator.heatOperator t f :=
  rfl

/-- Positive right-hand heat difference quotient as a linear map. The zero branch is irrelevant on
`Ioi 0` but makes the family total on `NNReal`. -/
noncomputable def twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : NNReal) : C(G, ℝ) →ₗ[ℝ] C(G, ℝ) :=
  if ht : 0 < t then
    ((t : ℝ)⁻¹) •
      (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge (t : ℝ)
        (by exact_mod_cast ht) - LinearMap.id)
  else 0

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_zero
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge 0 = 0 := by
  unfold twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap
  rw [dif_neg]
  simp

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact continuous-function form of the positive difference quotient. -/
theorem twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f =
      ((t : ℝ)⁻¹) •
        (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f - f) := by
  unfold twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap
  rw [dif_pos ht]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact pointwise scalar quotient represented by the bundled linear map. -/
theorem twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply_point
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f g =
      (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g - f g) /
        (t : ℝ) := by
  rw [twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply bridge t ht f]
  simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
    ContinuousMap.coe_sub, Pi.sub_apply]
  rw [div_eq_mul_inv, mul_comm]

end

end Dimensions
end YangMills
