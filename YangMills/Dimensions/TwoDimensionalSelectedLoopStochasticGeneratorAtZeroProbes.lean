/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopStochasticGeneratorAtZero

/-!
# Hostile probes for the selected-loop stochastic generator at zero
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
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Explicit heat-trajectory and pairing-generator boundary continuity construct the genuine
zero-time generator obligation by one-sided extension of derivatives. -/
theorem exact_boundaryContinuity_toGeneratorAtZero
    (data : TwoDimensionalSelectedLoopGeneratorBoundaryContinuityData bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge :=
  data.toStochasticGeneratorAtZeroData

omit [FiniteDimensional ℝ E] in
/-- Operator and stochastic right-increment formulations are exactly equivalent on the unchanged
bridge. -/
theorem exact_zeroTimeGenerator_semantics_equivalent :
    bridge.HasOperatorGeneratorAtZero ↔ bridge.HasStochasticRightIncrementGeneratorAtZero :=
  bridge.operatorGeneratorAtZero_iff_stochasticRightIncrementGeneratorAtZero

omit [FiniteDimensional ℝ E] in
/-- Positive probe: zero-time operator regularity yields the exact Brownian increment generator at
every deterministic base time. -/
theorem exact_stochasticRightIncrementGeneratorAtZero
    (data : TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge) :
    bridge.HasStochasticRightIncrementGeneratorAtZero :=
  data.stochasticRightIncrementGeneratorAtZero

omit [FiniteDimensional ℝ E] in
/-- Hostile probe: the same stochastic difference quotient cannot converge to a changed generator
value. -/
theorem changed_stochasticGeneratorAtZero_blocked
    (data : TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge)
    (s : NNReal) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G)
    (changed : ℝ)
    (changed_ne_exact : changed ≠ (1 / 2 : ℝ) * realLaplacian.laplacian f g)
    (claimed :
      Tendsto
        (fun t : NNReal =>
          ((∫ samplePoint,
              f (g * ((bridge.brownian.process s samplePoint)⁻¹ *
                bridge.brownian.process (s + t) samplePoint))
              ∂bridge.brownian.probabilityMeasure) - f g) / (t : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False := by
  have exact := data.stochasticRightIncrementGeneratorAtZero s f g
  exact changed_ne_exact (tendsto_nhds_unique claimed exact)

end

end YangMills.Dimensions
