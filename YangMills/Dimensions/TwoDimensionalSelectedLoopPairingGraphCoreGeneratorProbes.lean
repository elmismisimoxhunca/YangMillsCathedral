/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopPairingGraphCoreGenerator

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
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact probe: graph-core data gives uniform-norm generation on every smooth test. -/
theorem exact_pairingGraphCore_allSmooth_generator
    (data : TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData bridge)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    Tendsto
      (fun t : NNReal => twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian) f)) :=
  TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData.allSmooth_generator data f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact probe: the graph-core record constructs the established stochastic generator endpoint. -/
theorem exact_pairingGraphCore_stochasticGenerator
    (data : TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData bridge) :
    Nonempty (TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge) :=
  ⟨TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData.toStochasticGeneratorAtZeroData data⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile probe: the uniform-norm generator target cannot be changed. -/
theorem changed_pairingGraphCore_generator_target_blocked
    (data : TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData bridge)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian) f)
    (claimed : Tendsto
      (fun t : NNReal => twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData.allSmooth_generator data f))

end

end Dimensions
end YangMills
