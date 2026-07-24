/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance

/-!
# Hostile probes for proposition-shaped current-strength 2D literature acceptance
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
  uGeneralTargetEdge uGeneralTargetInternal uGeneralTargetFace uGeneralTargetRegion
  uGeneralTargetSurface uGeneralTargetVertex uGeneralSourceFineEdge uGeneralSourceFineInternal
  uGeneralSourceFineFace uGeneralSourceFineVertex uGeneralTargetFineEdge
  uGeneralTargetFineInternal uGeneralTargetFineFace uGeneralTargetFineVertex
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

namespace TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptanceProbes

variable (acceptance : TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection, uΩ,
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

include acceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The proposition exposes all six flattened top-level literature components without synthesizing
any of them. -/
theorem exact_flat_component_audit :
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
      (SenguptaTargetSurface := SenguptaTargetSurface)) :=
  TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.iff_flat_components.mp acceptance

include acceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Positive projection: the proposition retains exact rank two. -/
theorem exact_rank_two : Module.finrank ℝ EG = 2 :=
  TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.model_finrank_two acceptance

include acceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Hostile dimension probe: the proposition cannot be weakened to a dimension-free witness. -/
theorem four_dimensional_linear_model_blocked :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.not_linearEquiv_four acceptance

/-- `True` cannot replace the acceptance proposition while retaining its dimensional conclusion. -/
theorem truth_surrogate_does_not_reject_four :
    ¬ (True → ¬ Nonempty
      (EuclideanDimension.four.Spacetime ≃ₗ[ℝ] EuclideanDimension.four.Spacetime)) := by
  intro claimed
  exact claimed trivial ⟨LinearEquiv.refl ℝ _⟩


include acceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The prior source acceptance directly constructs its full-past strengthening. -/
theorem exact_current_implies_fullPast :
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
    (SenguptaTargetSurface := SenguptaTargetSurface) :=
  TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.ofCurrent acceptance

variable (fullAcceptance : TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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



include fullAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Forgetting the finite-cylinder/full-past field recovers the exact unchanged prior proposition. -/
theorem exact_fullPast_implies_current :
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
      (SenguptaTargetSurface := SenguptaTargetSurface) :=
  TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.implies_current
    fullAcceptance

include fullAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The strengthened proposition exposes the exact prior components and their dependent derived
finite-cylinder transition record from which full-past semantics is constructed. -/
theorem exact_fullPast_component_audit :
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
        source.current.planar.toSpectralBrownianGeneratorBridgeData) :=
  TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.iff_components.mp
    fullAcceptance

include fullAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Full-past strengthening retains rank two. -/
theorem exact_fullPast_rank_two : Module.finrank ℝ EG = 2 :=
  TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.model_finrank_two
    fullAcceptance

include fullAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Full-past strengthening cannot change the actual model into four-dimensional spacetime. -/
theorem fullPast_four_dimensional_linear_model_blocked :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  TwoDimensionalFullPastCurrentStrengthSourceIndexedLiteratureAcceptance.not_linearEquiv_four
    fullAcceptance


variable (generatorAcceptance : TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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

variable (selectedFourierAcceptance :
    TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact source-indexed Fourier/derivative join reaches the direct all-smooth operator generator. -/
noncomputable def exact_selectedFourierDerivative_sourceJoin_operatorGenerator :=
  TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.implies_operatorGenerator
    selectedFourierAcceptance

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact direct operator-generator forgetting projection to unchanged current strength. -/
noncomputable def exact_operatorGenerator_sourceJoin_current :=
  TwoDimensionalOperatorGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.implies_current
    (exact_selectedFourierDerivative_sourceJoin_operatorGenerator selectedFourierAcceptance)

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The direct operator-generator source acceptance retains exact rank two. -/
theorem exact_operatorGenerator_sourceJoin_rank_two : Module.finrank ℝ EG = 2 :=
  TwoDimensionalOperatorGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.model_finrank_two
    (exact_selectedFourierDerivative_sourceJoin_operatorGenerator selectedFourierAcceptance)

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The direct operator-generator source acceptance rejects a four-dimensional model. -/
theorem operatorGenerator_sourceJoin_four_dimensional_linear_model_blocked :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  TwoDimensionalOperatorGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.not_linearEquiv_four
    (exact_selectedFourierDerivative_sourceJoin_operatorGenerator selectedFourierAcceptance)

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Hostile source-join probe: an accepted Fourier/derivative source cannot coexist with failure of
the direct operator-generator acceptance. -/
theorem selectedFourierDerivative_sourceJoin_missing_operatorGenerator_blocked
    (missing : ¬ TwoDimensionalOperatorGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge, uSample, uConnection,
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
      (SenguptaTargetSurface := SenguptaTargetSurface)) : False :=
  missing
    (TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.implies_operatorGenerator
      selectedFourierAcceptance)

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Source-indexed Fourier/derivative strengthening retains exact rank two. -/
theorem exact_selectedFourierDerivative_sourceJoin_rank_two : Module.finrank ℝ EG = 2 :=
  TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.model_finrank_two
    selectedFourierAcceptance

include selectedFourierAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Source-indexed Fourier/derivative strengthening cannot become the four-dimensional model. -/
theorem selectedFourierDerivative_sourceJoin_four_dimensional_linear_model_blocked :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  TwoDimensionalSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptance.not_linearEquiv_four
    selectedFourierAcceptance

include generatorAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Exact zero-time generator inhabitance audit on the unchanged source components. -/
theorem exact_stochasticGenerator_component_audit :
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
          source.current.planar.toSpectralBrownianGeneratorBridgeData) :=
  TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.iff_components.mp generatorAcceptance



include generatorAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The audited pairing-generator boundary limit constructs the exact operator/stochastic generator witness. -/
theorem exact_stochasticGenerator_constructed_from_boundaries :
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
          source.current.planar.toSpectralBrownianGeneratorBridgeData) :=
  TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.generatorAtZero generatorAcceptance

include generatorAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Forgetting the zero-time generator field recovers the prior source acceptance. -/
theorem exact_stochasticGenerator_implies_current :
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
    (SenguptaTargetSurface := SenguptaTargetSurface) :=
  TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.implies_current generatorAcceptance

include generatorAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Zero-time generator strengthening remains exactly rank two. -/
theorem exact_stochasticGenerator_rank_two : Module.finrank ℝ EG = 2 :=
  TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.model_finrank_two generatorAcceptance

include generatorAcceptance in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Zero-time generator strengthening cannot become the four-dimensional model. -/
theorem stochasticGenerator_four_dimensional_linear_model_blocked :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  TwoDimensionalStochasticGeneratorCurrentStrengthSourceIndexedLiteratureAcceptance.not_linearEquiv_four generatorAcceptance

variable
  (generalFactThreeData :
    TwoDimensionalGeneralFactThreeCurrentStrengthSourceIndexedLiteratureAcceptanceData.{uE, uG,
      uGauge, uSample, uConnection, uΩ, uVertex, uEdge, uFace, uXAxisCell, uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace,
      uFineXAxisCell, uFineLargeVertex, uFineLargeEdge, uFineLargeFace, uFineLargeXAxisCell,
      uEL, uHL, uSL, uER, uHR, uSR, uEG, uHG, uLeftBase, uRightBase, uWholeBase,
      uLeftLoop, uRightLoop, uWholeLoop, uLeftSample, uRightSample, uWholeSample, uCover,
      uCurveS, uEdgeS, uInternalEdge, uFaceS, uRegionS, uSenguptaSample, uSenguptaSurface,
      uSenguptaBaseVertex, uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex,
      uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
      uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface,
      uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex,
      uGeneralTargetEdge, uGeneralTargetInternal, uGeneralTargetFace, uGeneralTargetRegion,
      uGeneralTargetSurface, uGeneralTargetVertex, uGeneralSourceFineEdge,
      uGeneralSourceFineInternal, uGeneralSourceFineFace, uGeneralSourceFineVertex,
      uGeneralTargetFineEdge, uGeneralTargetFineInternal, uGeneralTargetFineFace,
      uGeneralTargetFineVertex, uPath, uObservable}
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

include generalFactThreeData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The general-Fact-3 strengthening forgets to the unchanged current-strength source witness. -/
theorem exact_generalFactThree_implies_current :
    TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptance.{uE, uG, uGauge,
      uSample, uConnection, uΩ, uVertex, uEdge, uFace, uXAxisCell, uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineVertex, uFineEdge, uFineFace,
      uFineXAxisCell, uFineLargeVertex, uFineLargeEdge, uFineLargeFace,
      uFineLargeXAxisCell, uEL, uHL, uSL, uER, uHR, uSR, uEG, uHG, uLeftBase,
      uRightBase, uWholeBase, uLeftLoop, uRightLoop, uWholeLoop, uLeftSample,
      uRightSample, uWholeSample, uCover, uCurveS, uEdgeS, uInternalEdge, uFaceS,
      uRegionS, uSenguptaSample, uSenguptaSurface, uSenguptaBaseVertex,
      uSenguptaFineInternal, uSenguptaFineFace, uSenguptaFineVertex,
      uSenguptaTargetEdge, uSenguptaTargetInternal, uSenguptaTargetFace,
      uSenguptaTargetRegion, uSenguptaTargetVertex, uSenguptaTargetSurface,
      uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex,
      uPath, uObservable}
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
  generalFactThreeData.implies_current

include generalFactThreeData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- General Fact 3 acceptance remains exactly rank two. -/
theorem exact_generalFactThree_rank_two : Module.finrank ℝ EG = 2 :=
  generalFactThreeData.model_finrank_two

include generalFactThreeData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- General Fact 3 acceptance cannot become a four-dimensional linear model. -/
theorem generalFactThree_four_dimensional_linear_model_blocked :
    ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  generalFactThreeData.not_linearEquiv_four

include generalFactThreeData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Hostile dependency probe: the fixed-universe general candidate class cannot be empty. -/
theorem generalFactThree_empty_candidate_class_blocked
    (empty : ¬Nonempty
      (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSurface, uSenguptaBaseVertex,
        uGeneralTargetEdge, uGeneralTargetInternal, uGeneralTargetFace, uGeneralTargetRegion,
        uGeneralTargetSurface, uGeneralTargetVertex}
        (baseEmbedded := (Classical.choice generalFactThreeData.current).compactFiniteLaw.current
          |>.embeddedFiniteLaw.embeddedBase))) : False :=
  empty generalFactThreeData.generalFactThree.candidate_nonempty

variable
  (generalFactThreeFourierData :
    TwoDimensionalGeneralFactThreeSelectedFourierDerivativeCurrentStrengthSourceIndexedLiteratureAcceptanceData.{uE,
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
      uCandidateFineEdge, uCandidateFineInternal, uCandidateFineFace, uCandidateFineVertex,
      uGeneralTargetEdge, uGeneralTargetInternal, uGeneralTargetFace, uGeneralTargetRegion,
      uGeneralTargetSurface, uGeneralTargetVertex, uGeneralSourceFineEdge,
      uGeneralSourceFineInternal, uGeneralSourceFineFace, uGeneralSourceFineVertex,
      uGeneralTargetFineEdge, uGeneralTargetFineInternal, uGeneralTargetFineFace,
      uGeneralTargetFineVertex, uPath, uObservable}
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

include generalFactThreeFourierData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The joint acceptance retains the nonempty universal general-Fact-3 candidate class selected by
its exact source component. -/
theorem exact_generalFactThreeFourier_source :
    Nonempty
      (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurveS, uEdgeS,
        uInternalEdge, uFaceS, uRegionS, uSenguptaSurface, uSenguptaBaseVertex,
        uGeneralTargetEdge, uGeneralTargetInternal, uGeneralTargetFace, uGeneralTargetRegion,
        uGeneralTargetSurface, uGeneralTargetVertex}
        (baseEmbedded := (Classical.choice generalFactThreeFourierData.source.current)
          |>.compactFiniteLaw.current.embeddedFiniteLaw.embeddedBase)) :=
  generalFactThreeFourierData.source.generalFactThree.candidate_nonempty

include generalFactThreeFourierData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The joint acceptance exposes the exact four selected-Fourier derivative obligations. -/
theorem exact_generalFactThreeFourier_analytic :
    TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance
      ((Classical.choice generalFactThreeFourierData.source.current).augmented.current.planar
        |>.toSpectralBrownianGeneratorBridgeData) :=
  generalFactThreeFourierData.selectedFourierDerivative

include generalFactThreeFourierData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The joint acceptance remains rank two and rejects a 4D linear model. -/
theorem exact_generalFactThreeFourier_dimension_contract :
    Module.finrank ℝ EG = 2 ∧
      ¬ Nonempty (EG ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) :=
  ⟨generalFactThreeFourierData.source.model_finrank_two,
    generalFactThreeFourierData.source.not_linearEquiv_four⟩

include generalFactThreeFourierData in
omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- Hostile analytic probe: omitting the exact selected-Fourier derivative obligations is rejected. -/
theorem missing_generalFactThreeFourier_analytic_blocked
    (missing : ¬TwoDimensionalSelectedLoopSmoothMatrixCoefficientSelectedFourierDerivativeAnalyticAcceptance
      ((Classical.choice generalFactThreeFourierData.source.current).augmented.current.planar
        |>.toSpectralBrownianGeneratorBridgeData)) : False :=
  missing generalFactThreeFourierData.selectedFourierDerivative

end TwoDimensionalCurrentStrengthSourceIndexedLiteratureAcceptanceProbes

end

end YangMills.Dimensions
