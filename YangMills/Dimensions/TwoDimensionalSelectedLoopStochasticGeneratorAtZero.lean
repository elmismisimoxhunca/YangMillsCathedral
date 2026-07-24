/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastCylinderPiSystem

/-!
# Selected-loop stochastic generator at time zero

Positive-time heat differentiation is already part of the spectral Brownian bridge. The genuine
stochastic generator additionally requires a right-hand difference-quotient limit at elapsed time
zero on smooth tests. This module states that remaining boundary regularity precisely and proves
that it is equivalent to the corresponding Brownian right-increment expectation limit.
-/

namespace YangMills.Dimensions

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

/-- A smooth scalar test packaged as the continuous test required by the heat operator. -/
def smoothLieGroupScalarContinuousMap
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) : C(G, ℝ) where
  toFun := f
  continuous_toFun := f.contMDiff.continuous

/-- Exact right-hand operator-generator semantics at elapsed time zero. The domain is `NNReal`, so
only physical nonnegative elapsed times occur; `Ioi 0` excludes the zero denominator. -/
def TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.HasOperatorGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
    Tendsto
      (fun t : NNReal =>
        (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ)
            (smoothLieGroupScalarContinuousMap f) g - f g) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g))

/-- Exact Brownian right-increment difference-quotient semantics. It quantifies over every
deterministic base time and group point and uses the unchanged process measure. -/
def TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.HasStochasticRightIncrementGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) : Prop :=
  ∀ (s : NNReal) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G),
    Tendsto
      (fun t : NNReal =>
        ((∫ samplePoint,
            f (g * ((bridge.brownian.process s samplePoint)⁻¹ *
              bridge.brownian.process (s + t) samplePoint))
            ∂bridge.brownian.probabilityMeasure) - f g) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * realLaplacian.laplacian f g))

/-- Explicit remaining zero-time regularity obligation. Positive-time differentiation alone does
not supply this boundary limit, so no inhabitant is fabricated here. -/
structure TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  operatorGeneratorAtZero : bridge.HasOperatorGeneratorAtZero

omit [FiniteDimensional ℝ E] in
/-- The exact positive-time operator/increment expectation identity transports the supplied
zero-time operator generator to the genuine stochastic right-increment generator, for every base
time. -/
theorem TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData.stochasticRightIncrementGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge) :
    bridge.HasStochasticRightIncrementGeneratorAtZero := by
  intro s f g
  apply (data.operatorGeneratorAtZero f g).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_pos : 0 < t := ht
  rw [bridge.generated_operator_eq_rightIncrementExpectation g s t ht_pos
    (smoothLieGroupScalarContinuousMap f)]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Operator and stochastic right-increment zero-time generator semantics are equivalent. The
reverse implication uses one deterministic base time; stationary increments then recover all base
times through the forward implication. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.operatorGeneratorAtZero_iff_stochasticRightIncrementGeneratorAtZero
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) :
    bridge.HasOperatorGeneratorAtZero ↔ bridge.HasStochasticRightIncrementGeneratorAtZero := by
  constructor
  · intro operatorGenerator
    exact (TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData.mk operatorGenerator).stochasticRightIncrementGeneratorAtZero
  · intro stochasticGenerator f g
    have atBaseZero := stochasticGenerator 0 f g
    apply atBaseZero.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    rw [bridge.generated_operator_eq_rightIncrementExpectation g 0 t ht_pos
      (smoothLieGroupScalarContinuousMap f)]
    rfl

end

end YangMills.Dimensions
