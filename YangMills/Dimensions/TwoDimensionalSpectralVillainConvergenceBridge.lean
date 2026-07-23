/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalDriverVillainConvergence
import YangMills.Dimensions.TwoDimensionalSpectralVillainProductIdentityBridge

/-!
# Spectral Villain bridge to Driver Theorem 8.5 convergence

The spectral chain now supplies the exact all-spacing Theorem 7.2 weak limits and the enlarged
`VB(ε)` product identity for the literal Villain action `Q_{ε²}`. Driver Theorem 8.5 then has one
remaining analytic field: convergence of the varying finite selected-density integrals to the
unchanged enlarged continuum heat integral.

`TwoDimensionalSpectralVillainConvergenceBridgeData` ties that exact uninhabited field to the same
spectral representation/pairing/heat/kernel chain, graph approximations, face geometry, product
identity, and continuum expectation law. The existing theorem then derives convergence of every
continuous coarse observable to its unchanged continuum holonomy expectation.

No graph family, continuum expectation law, weak limit, analytic convergence theorem, or Yang–Mills
measure is constructed.
-/

namespace YangMills
namespace Dimensions

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

/-- Exact final analytic Driver 8.5 obligation attached to the spectral product bridge. -/
structure TwoDimensionalSpectralVillainConvergenceBridgeData where
  productBridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
    (faceGeometry := faceGeometry)
  convergence : TwoDimensionalDriverVillainConvergenceData
    productBridge.weakLimitFamily.spectralWilson.toVillainCommonHeatChainCoreData
    axial continuum coarseApproximation enlargedApproximation faceGeometry

namespace TwoDimensionalSpectralVillainConvergenceBridgeData

/-- Exact Driver-convergence inhabitation debt: an exact spectral product bridge together with the
remaining varying-finite-graph convergence theorem on its unchanged common heat chain. -/
theorem nonempty_iff_productBridge_convergence :
    Nonempty (TwoDimensionalSpectralVillainConvergenceBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry)) ↔
      ∃ productBridge : TwoDimensionalSpectralVillainProductIdentityBridgeData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
        (faceGeometry := faceGeometry),
      Nonempty (TwoDimensionalDriverVillainConvergenceData
        productBridge.weakLimitFamily.spectralWilson.toVillainCommonHeatChainCoreData
        axial continuum coarseApproximation enlargedApproximation faceGeometry) := by
  constructor
  · rintro ⟨bridge⟩
    exact ⟨bridge.productBridge, ⟨bridge.convergence⟩⟩
  · rintro ⟨productBridge, ⟨convergence⟩⟩
    exact ⟨⟨productBridge, convergence⟩⟩

/-- Driver's existing convergence certificate with the exact spectral Villain common heat chain. -/
abbrev driverConvergence
    (bridge : TwoDimensionalSpectralVillainConvergenceBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry)) :=
  bridge.convergence

/-- Every continuous coarse observable converges from the exact spectral Villain lattice laws to the
unchanged continuum holonomy expectation. -/
theorem everyContinuous_latticeExpectation_tendsto_continuum
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
  bridge.convergence.everyContinuous_latticeExpectation_tendsto_continuum
    bridge.productBridge.weakLimitFamily.spectralWilson.toVillainCommonHeatChainCoreData
    axial continuum coarseApproximation enlargedApproximation faceGeometry
    bridge.productBridge.toDriverAxialLatticeProductIdentityData observable continuous

end TwoDimensionalSpectralVillainConvergenceBridgeData

end

end Dimensions
end YangMills
