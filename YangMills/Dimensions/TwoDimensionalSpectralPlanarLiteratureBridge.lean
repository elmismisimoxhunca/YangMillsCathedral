/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridge
import YangMills.Dimensions.TwoDimensionalSpectralVillainConvergenceBridge

/-!
# One planar 2D literature chain from spectral Brownian heat to lattice convergence

This bridge joins the previously separate Brownian and Driver lattice-convergence tracks without an
external equality field. The supplied Brownian process is dependently indexed by the exact spectral
semigroup and real heat core already used by the all-spacing Villain weak limits, enlarged product
identity, and Theorem 8.5 convergence chain.

It constructs the existing spectral Brownian/generated-operator bridge and therefore inherits the
spectral increment, two-time, and weak current-state Markov conclusions. It simultaneously retains
the every-continuous-observable lattice-to-planar-continuum limit. No process, graph family, weak
limit, product identity, convergence theorem, or Yang–Mills measure is constructed.
-/

namespace YangMills
namespace Dimensions

open Filter MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ
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
    {Ω : Type uΩ} [MeasurableSpace Ω]
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

/-- One exact planar chain sharing the spectral heat core between Brownian and lattice convergence. -/
structure TwoDimensionalSpectralPlanarLiteratureBridgeData where
  convergence : TwoDimensionalSpectralVillainConvergenceBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
    (continuum := continuum) (faceGeometry := faceGeometry)
  brownian : TwoDimensionalSelectedLoopBrownianRealizationData
    inner law
      convergence.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel.convolutionSemigroup
      realLaplacian
      convergence.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel.heatEquationCore Ω

namespace TwoDimensionalSpectralPlanarLiteratureBridgeData

/-- Construct the existing spectral Brownian/generated-operator bridge from the exact same heat core
already used by Driver convergence. -/
noncomputable def toSpectralBrownianGeneratorBridgeData
    (bridge : TwoDimensionalSpectralPlanarLiteratureBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)) :
    TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω) where
  spectralHeatKernel :=
    bridge.convergence.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel
  brownian := bridge.brownian

/-- The joined planar chain retains Driver 8.5 convergence for every continuous coarse observable. -/
theorem everyContinuous_latticeExpectation_tendsto_continuum
    (bridge : TwoDimensionalSpectralPlanarLiteratureBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω))
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable) :
    Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(bridge.convergence.productBridge.weakLimitFamily.weakLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure)) :=
  bridge.convergence.everyContinuous_latticeExpectation_tendsto_continuum observable continuous

/-- The same joined chain retains the weak current-state Markov identity for its exact Brownian
process and generated operator. -/
theorem twoTime_weakMarkov_identity
    (bridge : TwoDimensionalSpectralPlanarLiteratureBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω))
    (s t : NNReal) (hs : 0 < s) (ht : 0 < t) (φ f : C(G, ℝ)) :
    (∫ samplePoint, φ (bridge.brownian.process s samplePoint) *
      f (bridge.brownian.process (s + t) samplePoint) ∂bridge.brownian.probabilityMeasure) =
      ∫ samplePoint, φ (bridge.brownian.process s samplePoint) *
        (bridge.convergence.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel.kernelOperator.heatOperator
          (t : ℝ) f (bridge.brownian.process s samplePoint))
        ∂bridge.brownian.probabilityMeasure :=
  bridge.toSpectralBrownianGeneratorBridgeData.twoTime_weakMarkov_identity s t hs ht φ f

end TwoDimensionalSpectralPlanarLiteratureBridgeData

end

end Dimensions
end YangMills
