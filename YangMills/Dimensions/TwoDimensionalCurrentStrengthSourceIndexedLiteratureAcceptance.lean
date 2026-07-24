/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptance
import YangMills.Dimensions.TwoDimensionalSelectedLoopStochasticGeneratorAtZero
import YangMills.Dimensions.TwoDimensionalSelectedLoopSmoothMatrixCoefficientGenerator

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


/-- Current-strength source components carrying the canonically constructed finite-past-cylinder
transition record and full-past Markov semantics on the exact Brownian/spectral bridge already
selected by the planar literature chain. -/
structure TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureComponents where
  source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)
  finitePastCylinderMarkov : TwoDimensionalSelectedLoopFinitePastCylinderMarkovData
    source.current.planar.toSpectralBrownianGeneratorBridgeData

/-- Proposition-shaped current-strength source index including the exact derived finite-cylinder
record that constructs full-past Markov semantics. It is equivalent to the prior current-strength
source proposition, remains uninhabited, and is not the final source-complete 2D target. -/
def TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance : Prop :=
  Nonempty
    (TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface))

namespace TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Any strengthened witness recovers the unchanged prior proposition-shaped source acceptance. -/
theorem implies_current
    (acceptance : TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) := by
  rcases acceptance with ⟨components⟩
  exact ⟨components.source.strongest⟩





omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The prior current-strength source proposition constructs its full-past strengthening: the
finite-cylinder field is now a theorem of its unchanged nested spectral Brownian bridge. -/
theorem ofCurrent
    (acceptance : TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) := by
  rcases acceptance with ⟨strongest⟩
  let source := TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.ofStrongest strongest
  exact ⟨⟨source,
    source.current.planar.toSpectralBrownianGeneratorBridgeData.toFinitePastCylinderMarkovData⟩⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Full-past strengthening introduces no new inhabitance hypothesis beyond the prior exact source
components. -/
theorem iff_current :
    TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) ↔ TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) :=
  ⟨implies_current, ofCurrent⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact component audit: the strengthening stores the prior six source components and their
canonically derived finite-cylinder transition record; the pi-system theorem constructs full-past
semantics from that record. -/
theorem iff_components :
    TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) ↔
    ∃ source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface),
      Nonempty (TwoDimensionalSelectedLoopFinitePastCylinderMarkovData
        source.current.planar.toSpectralBrownianGeneratorBridgeData) := by
  constructor
  · rintro ⟨components⟩
    exact ⟨components.source, ⟨components.finitePastCylinderMarkov⟩⟩
  · rintro ⟨source, ⟨finitePastCylinderMarkov⟩⟩
    exact ⟨⟨source, finitePastCylinderMarkov⟩⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The strengthened proposition retains exact rank two. -/
theorem model_finrank_two
    (acceptance : TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    Module.finrank ℝ EG = 2 := by
  rcases acceptance with ⟨components⟩
  exact components.source.strongest.compactSurface_model_finrank_two

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Adding full-past stochastic semantics cannot erase the two-versus-four dimensional contract. -/
theorem not_linearEquiv_four
    (acceptance : TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rcases acceptance with ⟨components⟩
  exact components.source.strongest.compactSurface_model_not_linearEquiv_four

end TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance


/-- Current-strength source-indexed 2D acceptance strengthened by the genuine zero-time stochastic
generator obligation on the unchanged nested spectral Brownian bridge. Unlike full-past Markov
conditioning, this boundary regularity is not yet derived. -/
def TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance : Prop :=
  ∃ source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface),
    Nonempty (TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData
      source.current.planar.toSpectralBrownianGeneratorBridgeData)

namespace TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact inhabitance audit: the prior six source components plus the dependent zero-time generator
witness, with no synthesized field. -/
theorem iff_components :
    TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) ↔
      ∃ source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface),
        Nonempty (TwoDimensionalSelectedLoopPairingGeneratorBoundaryContinuityData
          source.current.planar.toSpectralBrownianGeneratorBridgeData) := by
  rfl



omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The pairing-generator boundary-continuity limit constructs the actual zero-time operator/stochastic generator
witness on the same source components. -/
theorem generatorAtZero
    (acceptance : TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    ∃ source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface),
        Nonempty (TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData
          source.current.planar.toSpectralBrownianGeneratorBridgeData) := by
  rcases acceptance with ⟨source, ⟨boundary⟩⟩
  exact ⟨source, ⟨boundary.toBoundaryContinuityData.toStochasticGeneratorAtZeroData⟩⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Forgetting zero-time generator regularity recovers the unchanged current-strength source
acceptance. -/
theorem implies_current
    (acceptance : TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface) := by
  rcases acceptance with ⟨source, _⟩
  exact ⟨source.strongest⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Zero-time generator strengthening retains exact rank two. -/
theorem model_finrank_two
    (acceptance : TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) : Module.finrank ℝ EG = 2 := by
  rcases acceptance with ⟨source, _⟩
  exact source.strongest.compactSurface_model_finrank_two

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Zero-time generator strengthening cannot change the model into four-dimensional spacetime. -/
theorem not_linearEquiv_four
    (acceptance : TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface)) :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rcases acceptance with ⟨source, _⟩
  exact source.strongest.compactSurface_model_not_linearEquiv_four

end TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance

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

/-- Current-strength source-indexed Driver--Lévy--Sengupta acceptance augmented on its unchanged
nested spectral bridge by the exact four selected-Fourier/rescaled-derivative obligations. This is a
new conditional validation surface, not an inhabitance claim and not a final 2D theorem. -/
def TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance : Prop :=
  ∃ source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface),
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance
      source.current.planar.toSpectralBrownianGeneratorBridgeData

/-- Source-indexed current-strength acceptance augmented directly by an inhabited all-smooth
zero-time operator/stochastic generator datum on the unchanged nested bridge. This is deliberately
distinct from the earlier boundary-continuity strengthening. -/
def TwoDimensionalOperatorGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance : Prop :=
  ∃ source : TwoDimensionalCurrentStrengthSourceIndexedLiteratureComponents.{uE, uG, uGauge, uSample, uConnection,
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
    (SenguptaTargetSurface := SenguptaTargetSurface),
    Nonempty (TwoDimensionalSelectedLoopStochasticGeneratorAtZeroData
      source.current.planar.toSpectralBrownianGeneratorBridgeData)

namespace TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The selected-Fourier derivative source acceptance constructs the direct all-smooth generator
source acceptance by the already verified analytic chain. -/
theorem implies_operatorGenerator
    (acceptance : TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    TwoDimensionalOperatorGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
      (SenguptaTargetSurface := SenguptaTargetSurface) := by
  rcases acceptance with ⟨source, analytic⟩
  exact ⟨source, ⟨analytic.toStochasticGeneratorAtZeroData⟩⟩

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The source-indexed selected-Fourier derivative strengthening retains the exact descended
rank-two model. -/
theorem model_finrank_two
    (acceptance : TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    Module.finrank ℝ EG = 2 := by
  rcases acceptance with ⟨source, _analytic⟩
  exact source.strongest.compactSurface_model_finrank_two

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The source-indexed selected-Fourier derivative strengthening remains genuinely two-dimensional
and cannot identify its descended model with four-dimensional Euclidean spacetime. -/
theorem not_linearEquiv_four
    (acceptance : TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
      (SenguptaTargetSurface := SenguptaTargetSurface)) :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  rcases acceptance with ⟨source, _analytic⟩
  exact source.strongest.compactSurface_model_not_linearEquiv_four

end TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance

end

end YangMills.Dimensions
