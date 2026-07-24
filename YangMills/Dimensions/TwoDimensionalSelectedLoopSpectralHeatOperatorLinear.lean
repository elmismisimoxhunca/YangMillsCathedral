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

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The positive selected-loop heat operator is a contraction in the uniform norm. This follows
from its exact probability-measure representation and does not use a generator limit. -/
theorem twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_norm_le
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) :
    ‖twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f‖ ≤ ‖f‖ := by
  let μ := unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t
  letI : IsProbabilityMeasure μ := ⟨by
    exact unitaryMatrixDualCasimirHeatProbabilityMeasure_univ
      bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.casimirBridge
      bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.positivity ht⟩
  apply (ContinuousMap.norm_le (f :=
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f)
      (norm_nonneg f)).2
  intro g
  change ‖bridge.spectralHeatKernel.kernelOperator.heatOperator t f g‖ ≤ ‖f‖
  rw [bridge.generated_operator_eq_spectralMeasureIntegral t ht f g]
  calc
    ‖∫ x, f (g * x) ∂μ‖ ≤ ‖f‖ * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f (g * x))
    _ = ‖f‖ := by simp

/-- The positive selected-loop heat operator as a continuous real-linear contraction. -/
noncomputable def twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) : C(G, ℝ) →L[ℝ] C(G, ℝ) :=
  LinearMap.mkContinuous
    (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht) 1 (by
      intro f
      simpa using twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_norm_le bridge t ht f)

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap_apply
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) :
    twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap bridge t ht f =
      bridge.spectralHeatKernel.kernelOperator.heatOperator t f :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The bundled positive heat operator has operator norm at most one. -/
theorem twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap_norm_le_one
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) :
    ‖twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap bridge t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_norm_le bridge t ht f

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
/-- Contraction gives the elementary time-dependent bound `2 t⁻¹ ‖f‖` for the positive heat
difference quotient. Its singular time factor is explicit, so this theorem is not the eventual
uniform graph bound required for generator closure. -/
theorem twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_norm_le
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) :
    ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f‖ ≤
      2 * (t : ℝ)⁻¹ * ‖f‖ := by
  rw [twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply bridge t ht f,
    norm_smul, norm_inv, Real.norm_of_nonneg t.coe_nonneg]
  have hinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr t.coe_nonneg
  calc
    (t : ℝ)⁻¹ * ‖bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f - f‖
        ≤ (t : ℝ)⁻¹ *
          (‖bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f‖ + ‖f‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hinv
    _ ≤ (t : ℝ)⁻¹ * (‖f‖ + ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ hinv
      have hP := twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_norm_le
        bridge (t : ℝ) (by exact_mod_cast ht) f
      change ‖bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f‖ ≤ ‖f‖ at hP
      exact add_le_add hP le_rfl
    _ = 2 * (t : ℝ)⁻¹ * ‖f‖ := by ring

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
