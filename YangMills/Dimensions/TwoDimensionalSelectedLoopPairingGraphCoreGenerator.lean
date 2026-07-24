/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralHeatOperatorLinear

/-!
# Graph-core reduction of the selected-loop zero-time generator

This file instantiates the generic proper-domain graph-core closure theorem with:

* the smooth real scalar domain;
* its faithful map into `C(G, ℝ)`;
* one half of the canonical pairing-Laplacian linear map; and
* the bundled spectral heat difference quotients.

It packages graph density, an eventual uniform graph bound, and convergence on a designated core as
three explicit obligations. From them it derives the all-smooth-tests zero-time operator generator
and hence the existing stochastic-generator data. No core or inhabitant of the obligation record is
constructed here.
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

/-- One half of the canonical pairing Laplacian, as the exact proper-domain generator map. -/
noncomputable def twoDimensionalSelectedLoopPairingGeneratorLinearMap :
    SmoothLieGroupScalarFunction (E := E) (G := G) →ₗ[ℝ] C(G, ℝ) :=
  (1 / 2 : ℝ) • rightInvariantPairingLaplacianLinearMap realLaplacian

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem twoDimensionalSelectedLoopPairingGeneratorLinearMap_apply
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    twoDimensionalSelectedLoopPairingGeneratorLinearMap
      (realLaplacian := realLaplacian) f g =
      (1 / 2 : ℝ) * realLaplacian.laplacian f g := by
  simp [twoDimensionalSelectedLoopPairingGeneratorLinearMap,
    rightInvariantPairingLaplacianLinearMap_apply]

/-- Exact remaining graph-core obligations for extending the zero-time generator from a designated
smooth core to every smooth real test. -/
structure TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) where
  core : Set (SmoothLieGroupScalarFunction (E := E) (G := G))
  graphDense : IsLinearMapDomainGraphDenseCore
    smoothLieGroupScalarToContinuousLinearMap
    (twoDimensionalSelectedLoopPairingGeneratorLinearMap (realLaplacian := realLaplacian)) core
  graphBoundConstant : ℝ
  graphBoundConstant_nonneg : 0 ≤ graphBoundConstant
  eventual_graphBound : ∀ᶠ t : NNReal in nhdsWithin 0 (Set.Ioi 0),
    ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f)‖ ≤
        graphBoundConstant *
          (‖smoothLieGroupScalarToContinuousLinearMap f‖ +
            ‖twoDimensionalSelectedLoopPairingGeneratorLinearMap
              (realLaplacian := realLaplacian) f‖)
  core_generator : ∀ f ∈ core,
    Tendsto
      (fun t : NNReal => twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian) f))

namespace TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The three graph-core obligations imply uniform-norm generator convergence for every smooth test. -/
theorem allSmooth_generator
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData bridge) :
    ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      Tendsto
        (fun t : NNReal => twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f)) := by
  intro f
  exact tendsto_linearMapOnDomain_of_graphDenseAt_of_eventually_graphBound
    (𝕜 := ℝ) (D := SmoothLieGroupScalarFunction (E := E) (G := G))
    (X := C(G, ℝ)) (ι := NNReal) (l := nhdsWithin 0 (Set.Ioi 0))
    smoothLieGroupScalarToContinuousLinearMap
    (twoDimensionalSelectedLoopPairingGeneratorLinearMap (realLaplacian := realLaplacian))
    (twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge) data.core
    data.graphBoundConstant data.graphBoundConstant_nonneg data.eventual_graphBound
    data.core_generator (data.graphDense f)

/-- Graph-core convergence constructs the existing all-smooth-tests zero-time generator witness. -/
noncomputable def toStochasticGeneratorAtZeroData
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}
    (data : TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData bridge) :
    TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData bridge where
  operatorGeneratorAtZero := by
    intro f g
    have uniformLimit := data.allSmooth_generator f
    have evalLimit : Tendsto (ContinuousMap.evalCLM ℝ g)
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f))
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f g)) :=
      (ContinuousMap.evalCLM ℝ g).continuous.continuousAt
    have pointLimit := evalLimit.comp uniformLimit
    rw [twoDimensionalSelectedLoopPairingGeneratorLinearMap_apply] at pointLimit
    apply pointLimit.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    rw [Function.comp_apply]
    change twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
      (smoothLieGroupScalarToContinuousLinearMap f) g = _
    rw [twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply_point
      bridge t ht_pos (smoothLieGroupScalarToContinuousLinearMap f) g]
    rfl

end TwoDimensionalSelectedLoopPairingGraphCoreGeneratorData

end

end Dimensions
end YangMills
