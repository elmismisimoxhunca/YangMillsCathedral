/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalLevySmoothSewingBridge
import YangMills.Dimensions.TwoDimensionalSpectralPlanarLiteratureBridge

/-!
# Current-strength two-dimensional literature acceptance

This record is the first single acceptance surface joining:

* the source-indexed spectral heat/Brownian/Driver lattice weak-limit and Theorem 8.5 planar chain;
* smooth, oriented, measured compact-surface boundary gluing; and
* Lévy's exact inverse-boundary conditional sewing law.

Both tracks use the same compact gauge group `G`, while their sample carriers remain correctly
distinct. The record is hard-wired to the existing planar `ℝ²` lattice geometry, and the descended
surface model has derived real rank two.

This is explicitly **current-strength**, not yet the final 2D proposition. The existing literature
interfaces still do not prove a common planar-to-arbitrary-compact-surface heat-law construction,
full-past conditional Markov semantics, smooth quotient descent, the Brownian process, Driver's weak
limits/convergence, or Lévy's sewing kernels. No inhabitant is constructed here.
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
  uEL uHL uSL uER uHR uSR uEG uHG
  uLeftBase uRightBase uWholeBase uLeftLoop uRightLoop uWholeLoop
  uLeftSample uRightSample uWholeSample

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
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL]
    {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER]
    {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : Geometry.CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : Geometry.CompactSurfaceBoundaryOrientationData
      leftSurface leftPresentation}
    {rightSurface : Geometry.CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : Geometry.CompactSurfaceBoundaryOrientationData
      rightSurface rightPresentation}
    {identification : Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [MeasurableSpace EG] [BorelSpace EG]
    {HG : Type uHG} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    [IsManifold IG ∞ (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]

/-- Current-strength acceptance data for the joined planar and compact-surface 2D literature tracks,
using one exact gauge group and no four-dimensional endpoint machinery. -/
structure TwoDimensionalCurrentStrengthLiteratureAcceptanceData where
  planar : TwoDimensionalSpectralPlanarLiteratureBridgeData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
    (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
  compactSurface : TwoDimensionalLevySmoothSewingBridgeData
    (identification := identification) (IG := IG) (G := G)
    (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
    (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)

namespace TwoDimensionalCurrentStrengthLiteratureAcceptanceData

/-- The planar component retains every-continuous Driver lattice convergence. -/
theorem everyContinuous_latticeExpectation_tendsto_continuum
    (data : TwoDimensionalCurrentStrengthLiteratureAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (observable : (coarse.Edge → G) → ℝ) (continuous : Continuous observable) :
    Tendsto
      (fun spacing => ∫ configuration,
        observable (coarseApproximation.coarseRestriction spacing configuration)
          ∂(data.planar.convergence.productBridge.weakLimitFamily.weakLimit spacing).limitMeasure)
      positiveLatticeSpacingAtZero
      (nhds (∫ sample, observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure)) :=
  data.planar.everyContinuous_latticeExpectation_tendsto_continuum observable continuous

/-- Every designated probabilistic seam-loop point lies in the exact descended smooth interior. -/
theorem seamLoopTrace_mem_interior
    (data : TwoDimensionalCurrentStrengthLiteratureAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    data.compactSurface.sewing.wholeLoopTrace (data.compactSurface.sewing.seamBase pair)
        (data.compactSurface.sewing.seamLoop pair) circlePoint ∈
      IG.interior (Geometry.CompactSurfaceBoundaryGluingQuotient identification) :=
  data.compactSurface.seamLoopTrace_mem_interior pair circlePoint

/-- The actual descended compact-surface model has exact real dimension two. -/
theorem compactSurface_model_finrank_two
    (data : TwoDimensionalCurrentStrengthLiteratureAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :
    Module.finrank ℝ EG = 2 :=
  data.compactSurface.descent.glued_model_finrank_two

end TwoDimensionalCurrentStrengthLiteratureAcceptanceData

end

end Dimensions
end YangMills
