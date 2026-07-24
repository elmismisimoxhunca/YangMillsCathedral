/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSmoothMatrixCoefficientGenerator

namespace YangMills
namespace Dimensions

open Filter
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
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
/-- Exact real/imaginary matrix-coefficient heat action probe. -/
theorem exact_selectedLoopHeatOperator_smoothMatrixCoefficient
    (t : ℝ) (ht : 0 < t) (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)) =
      Real.exp (-(t / 2) * heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
        smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index) :=
  twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient bridge t ht index

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
include bridge in
/-- Exact derived real pairing-Laplacian eigenvalue probe. -/
theorem exact_selectedLoop_smoothMatrixCoefficient_laplacian
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) :
    realLaplacian.laplacian (smoothUnitaryMatrixCoefficientRealFunction index) g =
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian bridge index g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
include bridge in
/-- Hostile derived-Laplacian probe: changing the selected eigenvalue output is contradictory. -/
theorem changed_selectedLoop_smoothMatrixCoefficient_laplacian_blocked
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g)
    (claimed : realLaplacian.laplacian
      (smoothUnitaryMatrixCoefficientRealFunction index) g = changed) : False := by
  apply changed_ne_exact
  rw [← claimed]
  exact twoDimensionalSelectedLoop_smoothMatrixCoefficient_laplacian bridge index g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
include bridge in
/-- Exact constructed complex coefficientwise Casimir-bridge probe. -/
theorem exact_selectedLoop_constructedCoefficientCasimirBridge
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    complexLaplacian.laplacian (smoothUnitaryMatrixCoefficient ρ row column) g =
      -(heatTraceData.casimirWeight (unitaryMatrixDualClass
        ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) : ℂ) *
        smoothUnitaryMatrixCoefficient ρ row column g :=
  SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData.laplacian_smoothCoefficient
    (twoDimensionalSelectedLoopCoefficientCasimirLaplacianBridgeData bridge)
    ρ row column g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact uniform-norm zero-time generator probe for either real component. -/
theorem exact_selectedLoop_smoothMatrixCoefficient_generator
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealFunction index))) :=
  tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
    bridge index

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact finite-synthesis generator probe. -/
theorem exact_selectedLoop_smoothMatrixCoefficientSynthesis_generator
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealSynthesis coefficients)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealSynthesis coefficients))) :=
  tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficientSynthesis_generator
    bridge coefficients

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact fixed-range `core_generator` probe. -/
theorem exact_selectedLoop_smoothMatrixCoefficientCore_generator :
    ∀ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      Tendsto (fun t : NNReal =>
        twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
          (smoothLieGroupScalarToContinuousLinearMap f))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (twoDimensionalSelectedLoopPairingGeneratorLinearMap
          (realLaplacian := realLaplacian) f)) :=
  twoDimensionalSelectedLoop_smoothMatrixCoefficientCore_generator
    bridge

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The coefficient-specific reduction uses exactly the constructed matrix-coefficient range. -/
theorem exact_smoothMatrixCoefficientGraphCore_reduction_core
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) :
    data.toPairingGraphCoreGeneratorData.core =
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact debt probe: every coefficient-specific reduction supplies graph density for the fixed
matrix-coefficient range. -/
theorem exact_smoothMatrixCoefficientGraphCore_graphDense
    (data : TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) :
    IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :=
  data.graphDense

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile debt probe: absent graph density, the reduced coefficient graph-core record is
uninhabitable. -/
theorem missing_smoothMatrixCoefficientGraphDensity_blocks_reduction
    (missing : ¬ IsLinearMapDomainGraphDenseCore
      smoothLieGroupScalarToContinuousLinearMap
      (twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian))
      (smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))) :
    ¬ Nonempty (TwoDimensionalSelectedLoopSmoothMatrixCoefficientGraphCoreData bridge) := by
  rintro ⟨data⟩
  exact missing data.graphDense

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile heat-action probe: a changed real coefficient output is contradictory. -/
theorem changed_selectedLoopHeatOperator_smoothMatrixCoefficient_blocked
    (t : ℝ) (ht : 0 < t) (index : SmoothUnitaryMatrixCoefficientRealIndex E G)
    (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      Real.exp (-(t / 2) * heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
        smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index))
    (claimed : bridge.spectralHeatKernel.kernelOperator.heatOperator t
      (smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientRealFunction index)) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatOperator_smoothMatrixCoefficient bridge t ht index))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile generator probe: no changed target shares the uniform-norm right-hand limit. -/
theorem changed_selectedLoop_smoothMatrixCoefficient_generator_blocked
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      twoDimensionalSelectedLoopPairingGeneratorLinearMap
        (realLaplacian := realLaplacian)
        (smoothUnitaryMatrixCoefficientRealFunction index))
    (claimed : Tendsto (fun t : NNReal =>
      twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t
        (smoothLieGroupScalarToContinuousLinearMap
          (smoothUnitaryMatrixCoefficientRealFunction index)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_twoDimensionalSelectedLoop_smoothMatrixCoefficient_generator
      bridge index))

end

end Dimensions
end YangMills
