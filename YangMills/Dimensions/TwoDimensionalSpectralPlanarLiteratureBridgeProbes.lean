/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.FourDimensionalContractSeparation
import YangMills.Dimensions.TwoDimensionalSpectralPlanarLiteratureBridge

/-!
# Hostile probes for the joined planar 2D literature chain
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSpectralPlanarLiteratureBridge
namespace Probes

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

/-- Brownian and lattice convergence use the same spectral heat-kernel bridge definitionally. -/
theorem exact_shared_spectral_heat_kernel
    (bridge : TwoDimensionalSpectralPlanarLiteratureBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)) :
    bridge.toSpectralBrownianGeneratorBridgeData.spectralHeatKernel =
      bridge.convergence.productBridge.weakLimitFamily.spectralWilson.spectralHeatKernel :=
  rfl

/-- The joined chain retains exact every-continuous Driver convergence. -/
theorem exact_every_continuous_convergence
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
  bridge.everyContinuous_latticeExpectation_tendsto_continuum observable continuous

/-- The same chain retains the exact weak current-state Markov identity. -/
theorem exact_weak_markov
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
  bridge.twoTime_weakMarkov_identity s t hs ht φ f

/-- Hostile joined-chain probe: the Brownian probability measure cannot be zero. -/
theorem zero_brownian_measure_blocked
    (bridge : TwoDimensionalSpectralPlanarLiteratureBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω))
    (zeroMeasure : bridge.brownian.probabilityMeasure = 0) : False := by
  have normalized := bridge.brownian.probability_normalized
  rw [zeroMeasure] at normalized
  simp at normalized

/-- The joined planar chain remains intrinsically two-dimensional. -/
theorem not_four_dimensional :
    ¬ IsFourDimensionalClayEndpoint EuclideanDimension.two :=
  lowerDimension_not_clayEndpoint EuclideanDimension.two (Or.inr (Or.inl rfl))

end

end Probes
end TwoDimensionalSpectralPlanarLiteratureBridge
end Dimensions
end YangMills
