/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.FourDimensionalContractSeparation
import YangMills.Dimensions.TwoDimensionalSpectralVillainConvergenceBridge

/-!
# Hostile probes for the spectral Villain convergence bridge
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSpectralVillainConvergenceBridge
namespace Probes

open Filter MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    {axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)}
    {continuum : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial}
    {coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse)}
    {enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged)}
    {faceGeometry : TwoDimensionalDriverAxialLatticeFaceGeometryData
      (axial := axial) (coarseApproximation := coarseApproximation)
      (enlargedApproximation := enlargedApproximation)}

/-- The convergence contract uses the exact spectral Villain common heat chain. -/
theorem exact_spectral_common_heat_chain
    (bridge : TwoDimensionalSpectralVillainConvergenceBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry)) :
    bridge.productBridge.weakLimitFamily.spectralWilson.toVillainCommonHeatChainCoreData.heat =
        bridge.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel.heatEquationCore ∧
      bridge.productBridge.weakLimitFamily.spectralWilson.toVillainCommonHeatChainCoreData.kernel =
        bridge.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel.kernelOperator :=
  ⟨rfl, rfl⟩

/-- The final derived conclusion has the exact source quantifier over every continuous coarse
observable. -/
theorem exact_every_continuous_limit
    (bridge : TwoDimensionalSpectralVillainConvergenceBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry))
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable) :
    Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(bridge.productBridge.weakLimitFamily.weakLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure)) :=
  bridge.everyContinuous_latticeExpectation_tendsto_continuum observable continuous

/-- Hostile convergence probe: a claimed distinct limit contradicts uniqueness in the Hausdorff
real topology. -/
theorem changed_continuum_limit_blocked
    (bridge : TwoDimensionalSpectralVillainConvergenceBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry))
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable)
    (changed : ℝ)
    (changedLimit : Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(bridge.productBridge.weakLimitFamily.weakLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero (nhds changed))
    (different : changed ≠ ∫ sample, observable (fun edge =>
      base.holonomy (coarse.edgePath edge) (base.sampleConnection sample))
        ∂base.probabilityMeasure) : False := by
  apply different
  exact tendsto_nhds_unique changedLimit
    (bridge.everyContinuous_latticeExpectation_tendsto_continuum observable continuous)

/-- Driver's spectral Villain convergence conclusion remains two-dimensional. -/
theorem not_four_dimensional :
    ¬ IsFourDimensionalClayEndpoint EuclideanDimension.two :=
  lowerDimension_not_clayEndpoint EuclideanDimension.two (Or.inr (Or.inl rfl))

end

end Probes
end TwoDimensionalSpectralVillainConvergenceBridge
end Dimensions
end YangMills
