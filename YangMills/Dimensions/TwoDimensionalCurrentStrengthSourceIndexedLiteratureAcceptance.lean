/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptance

/-!
# Proposition-shaped source index for the assembled two-dimensional literature chain

This module closes the strongest currently assembled Driver--Lévy--Sengupta chain into a `Prop`,
rather than presenting only another data record. The proposition is exactly the nonemptiness of the
split-bond embedded-universal augmented witness, so it cannot hide a second, unrelated construction.

This is deliberately named `CurrentStrength`. It is not yet the final source-complete 2D target:
unrestricted/full Fact 2, general Fact 3, heat-factor integration, analytic and stochastic
inhabitation, and several source bridges remain open. No inhabitant is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff ENNReal

noncomputable section

universe uE uG uGauge uSample uConnection uΩ
  uVertex uEdge uFace uXAxisCell uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell
  uEL uHL uSL uER uHR uSR uEG uHG
  uLeftBase uRightBase uWholeBase uLeftLoop uRightLoop uWholeLoop
  uLeftSample uRightSample uWholeSample
  uCover uCurveS uEdgeS uInternalEdge uFaceS uRegionS uSenguptaSample
  uSenguptaSurface uSenguptaBaseVertex uSenguptaFineInternal uSenguptaFineFace
  uSenguptaFineVertex uSenguptaTargetEdge uSenguptaTargetInternal uSenguptaTargetFace
  uSenguptaTargetRegion uSenguptaTargetVertex uSenguptaTargetSurface
  uCandidateFineEdge uCandidateFineInternal uCandidateFineFace uCandidateFineVertex
  uPath uObservable

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
    {Connection : Type uConnection} {Ω : Type uΩ} [MeasurableSpace Ω]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData.{uG, uGauge, uSample, uConnection,
      uPath, uObservable} G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {inner : Geometry.InvariantInnerProductData (I := modelWithCornersSelf ℝ E) (G := G)}
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
    [MeasurableSpace EL] [BorelSpace EL] {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER] {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : Geometry.CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : Geometry.CompactSurfaceBoundaryOrientationData leftSurface leftPresentation}
    {rightSurface : Geometry.CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : Geometry.CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : Geometry.CompactSurfaceBoundaryOrientationData rightSurface rightPresentation}
    {identification : Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [MeasurableSpace EG] [BorelSpace EG] {HG : Type uHG} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    [IsManifold IG ∞ (Geometry.CompactSurfaceBoundaryGluingQuotient identification)]
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]
    {CoverGroup : Type uCover} [Group CoverGroup] [TopologicalSpace CoverGroup]
    [IsTopologicalGroup CoverGroup] [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {CurveS : Type uCurveS} [Fintype CurveS] [Nonempty CurveS]
    {EdgeS : Type uEdgeS} [Fintype EdgeS] [DecidableEq EdgeS]
    {InternalEdge : Type uInternalEdge} [Fintype InternalEdge] [DecidableEq InternalEdge]
    {FaceS : Type uFaceS} [Fintype FaceS] [DecidableEq FaceS]
    {RegionS : Type uRegionS} [Fintype RegionS] [DecidableEq RegionS]
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {SenguptaSurface : Type uSenguptaSurface} [TopologicalSpace SenguptaSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) SenguptaSurface]
    {SenguptaBaseVertex : Type uSenguptaBaseVertex}
    {SenguptaFineInternal : Type uSenguptaFineInternal}
    [Fintype SenguptaFineInternal] [DecidableEq SenguptaFineInternal]
    {SenguptaFineFace : Type uSenguptaFineFace}
    [Fintype SenguptaFineFace] [DecidableEq SenguptaFineFace]
    {SenguptaFineVertex : Type uSenguptaFineVertex}
    {senguptaFine : TwoDimensionalSenguptaTriangulatedRegionData
      EdgeS SenguptaFineInternal SenguptaFineFace RegionS}
    {SenguptaTargetEdge : Type uSenguptaTargetEdge}
    [Fintype SenguptaTargetEdge] [DecidableEq SenguptaTargetEdge]
    {SenguptaTargetInternal : Type uSenguptaTargetInternal}
    [Fintype SenguptaTargetInternal] [DecidableEq SenguptaTargetInternal]
    {SenguptaTargetFace : Type uSenguptaTargetFace}
    [Fintype SenguptaTargetFace] [DecidableEq SenguptaTargetFace]
    {SenguptaTargetRegion : Type uSenguptaTargetRegion} [DecidableEq SenguptaTargetRegion]
    {SenguptaTargetVertex : Type uSenguptaTargetVertex}
    {senguptaTarget : TwoDimensionalSenguptaTriangulatedRegionData
      SenguptaTargetEdge SenguptaTargetInternal SenguptaTargetFace SenguptaTargetRegion}
    {SenguptaTargetSurface : Type uSenguptaTargetSurface}
    [TopologicalSpace SenguptaTargetSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) SenguptaTargetSurface]

variable [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]

/-- Proposition-shaped current-strength acceptance surface for the exact assembled
Driver--Lévy--Sengupta chain. This definition packages no witness and proves no existence result. -/
def TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance : Prop :=
  Nonempty
    (TwoDimensionalSenguptaSplitBondEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface))

/-- Flattened literature-inhabitation components for the proposition-shaped current-strength 2D
surface. Every field is an existing source-facing witness; this structure constructs none of them. -/
structure TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents where
  gaugeGeometry : Geometry.CompactSimpleGaugeGroupData G E
  current : TwoDimensionalCurrentStrengthLiteratureAcceptanceData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
    (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
    (identification := identification) (IG := IG)
    (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
    (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
  finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
    (G := G) (CoverGroup := CoverGroup) (Curve := CurveS) (Edge := EdgeS)
    (Region := RegionS) (Sample := SenguptaSample)
  heatFactors : TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
    (planarSemigroup := current.planar.convergence.productBridge.weakLimitFamily.spectralWilson
      |>.spectralHeatKernel.convolutionSemigroup)
    (finiteLaw := finiteLaw) (coverDensity := coverDensity)
    (InternalEdge := InternalEdge) (Face := FaceS)
  finiteLawSewing : TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData
    finiteLaw current.compactSurface.sewing
  compactFiniteLaw :
    TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData.{uG, uCover,
      uGauge, uSample, uConnection, uCurveS, uEdgeS, uInternalEdge, uFaceS, uRegionS,
      uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex, uSenguptaFineInternal,
      uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge,
      uSenguptaTargetInternal, uSenguptaTargetFace, uSenguptaTargetRegion,
      uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge,
      uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex}
      (planarSemigroup := current.planar.convergence.productBridge.weakLimitFamily.spectralWilson
        |>.spectralHeatKernel.convolutionSemigroup)
      (finiteLaw := finiteLaw) (coverDensity := coverDensity)
      (heatFactors := heatFactors) (Surface := SenguptaSurface)
      (BaseVertex := SenguptaBaseVertex) (FineVertex := SenguptaFineVertex)
      (fine := senguptaFine) (TargetVertex := SenguptaTargetVertex)
      (target := senguptaTarget) (TargetSurface := SenguptaTargetSurface)

namespace TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents

/-- Reassemble the exact prior augmented chain from the flattened literature components. -/
noncomputable def augmented
    (components : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity) where
  gaugeGeometry := components.gaugeGeometry
  current := components.current
  finiteLaw := components.finiteLaw
  heatFactors := components.heatFactors
  finiteLawSewing := components.finiteLawSewing

/-- Reassemble the strongest exact wrapper without introducing any additional witness. -/
noncomputable def strongest
    (components : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalSenguptaSplitBondEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData.{uE,
      uG, uGauge, uSample, uConnection, uΩ, uVertex, uEdge, uFace, uXAxisCell,
      uLargeVertex, uLargeEdge, uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge,
      uFineFace, uFineXAxisCell, uFineLargeVertex, uFineLargeEdge, uFineLargeFace,
      uFineLargeXAxisCell, uEL, uHL, uSL, uER, uHR, uSR, uEG, uHG, uLeftBase,
      uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop, uLeftSample,
      uRightSample, uWholeSample, uCover, uCurveS, uEdgeS, uInternalEdge, uFaceS,
      uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
      uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex,
      uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
      uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface,
      uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface) where
  augmented := components.augmented
  compactFiniteLaw := components.compactFiniteLaw

/-- Flatten an existing strongest wrapper into its six source-facing construction components. -/
noncomputable def ofStrongest
    (data : TwoDimensionalSenguptaSplitBondEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData.{uE,
      uG, uGauge, uSample, uConnection, uΩ, uVertex, uEdge, uFace, uXAxisCell,
      uLargeVertex, uLargeEdge, uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge,
      uFineFace, uFineXAxisCell, uFineLargeVertex, uFineLargeEdge, uFineLargeFace,
      uFineLargeXAxisCell, uEL, uHL, uSL, uER, uHR, uSR, uEG, uHG, uLeftBase,
      uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop, uLeftSample,
      uRightSample, uWholeSample, uCover, uCurveS, uEdgeS, uInternalEdge, uFaceS,
      uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
      uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex,
      uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
      uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface,
      uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
      uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface) where
  gaugeGeometry := data.augmented.gaugeGeometry
  current := data.augmented.current
  finiteLaw := data.augmented.finiteLaw
  heatFactors := data.augmented.heatFactors
  finiteLawSewing := data.augmented.finiteLawSewing
  compactFiniteLaw := data.compactFiniteLaw

end TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents

namespace TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The proposition unfolds to exactly the strongest assembled witness type. -/
theorem iff_strongest_witness :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface) ↔
    Nonempty
      (TwoDimensionalSenguptaSplitBondEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
        (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
        (identification := identification) (IG := IG)
        (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
        (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
        (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
        (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
        (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
        (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
        (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
        (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
        (SenguptaTargetSurface := SenguptaTargetSurface)) :=
  Iff.rfl

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Fully flattened failed-inhabitation audit: the proposition is equivalent to supplying the exact
compact-simple geometry, current Driver/Lévy chain, Sengupta finite law, heat factors, finite-law
sewing bridge, and strongest dependent compact finite-law witness. -/
theorem iff_flat_components :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface) ↔
    Nonempty
      (TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
        uΩ, uVertex, uEdge, uFace, uXAxisCell,
        uLargeVertex, uLargeEdge, uLargeFace, uLargeXAxisCell, uFineVertex,
        uFineEdge, uFineFace, uFineXAxisCell, uFineLargeVertex, uFineLargeEdge,
        uFineLargeFace, uFineLargeXAxisCell, uEL, uHL, uSL,
        uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop,
        uWholeLoop, uLeftSample, uRightSample, uWholeSample, uCover,
        uCurveS, uEdgeS, uInternalEdge, uFaceS, uRegionS,
        uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex, uSenguptaFineInternal, uSenguptaFineFace,
        uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace, uSenguptaTargetRegion,
        uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.ofStrongest data⟩
  · rintro ⟨components⟩
    exact ⟨components.strongest⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact literature-only inhabitance audit at proposition level: acceptance is equivalent to the
prior augmented chain together with its dependently indexed strongest compact finite-law witness. -/
theorem iff_components :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface) ↔
    ∃ augmented : TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
        (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
        (identification := identification) (IG := IG)
        (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
        (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
        (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
        (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
        (SenguptaSample := SenguptaSample) (coverDensity := coverDensity),
      Nonempty
        (TwoDimensionalSenguptaSplitBondEmbeddedUniversalFiniteLawAcceptanceData.{uG,
          uCover, uGauge, uSample, uConnection, uCurveS, uEdgeS, uInternalEdge,
          uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
          uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex,
          uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
          uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface,
          uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
          uCandidateFineVertex}
          (planarSemigroup := augmented.current.planar.convergence.productBridge.weakLimitFamily
            |>.spectralWilson.spectralHeatKernel.convolutionSemigroup)
          (finiteLaw := augmented.finiteLaw) (coverDensity := coverDensity)
          (heatFactors := augmented.heatFactors) (Surface := SenguptaSurface)
          (BaseVertex := SenguptaBaseVertex) (FineVertex := SenguptaFineVertex)
          (fine := senguptaFine) (TargetVertex := SenguptaTargetVertex)
          (target := senguptaTarget) (TargetSurface := SenguptaTargetSurface)) :=
  iff_strongest_witness.trans
    TwoDimensionalSenguptaSplitBondEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData.nonempty_iff_components

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Proposition-level dimension contract: any inhabitant retains an actual descended model of exact
real rank two. -/
theorem model_finrank_two
    (acceptance : TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    Module.finrank ℝ EG = 2 := by
  rcases acceptance with ⟨data⟩
  exact data.compactSurface_model_finrank_two

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Proposition-level dimension contract: any inhabitant therefore rejects identification with
four-dimensional Euclidean spacetime. -/
theorem not_linearEquiv_four
    (acceptance : TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection, uΩ,
        uVertex, uEdge, uFace, uXAxisCell, uLargeVertex, uLargeEdge,
        uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell,
        uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell, uEL, uHL,
        uSL, uER, uHR, uSR, uEG, uHG,
        uLeftBase, uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop,
        uLeftSample, uRightSample, uWholeSample, uCover, uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
        uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex, uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
        uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface, uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace,
        uCandidateFineVertex, uPath, uObservable}
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
      (SenguptaSurface := SenguptaSurface) (SenguptaBaseVertex := SenguptaBaseVertex)
      (SenguptaFineVertex := SenguptaFineVertex) (senguptaFine := senguptaFine)
      (SenguptaTargetVertex := SenguptaTargetVertex) (senguptaTarget := senguptaTarget)
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rcases acceptance with ⟨data⟩
  exact data.compactSurface_model_not_linearEquiv_four

end TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance

end

end YangMills.Dimensions
