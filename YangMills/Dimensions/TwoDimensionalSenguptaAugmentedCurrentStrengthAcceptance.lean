/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalCurrentStrengthLiteratureAcceptance
import YangMills.Dimensions.TwoDimensionalSenguptaLevyFiniteHolonomyBridge
import YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptance

/-!
# Sengupta-augmented current-strength two-dimensional acceptance

This dependently joins the existing planar/Lévy current-strength record with one Sengupta finite law,
its covering heat and boundary-conditioned finite-face factor bridges, and its gauge-invariant
finite-law coherence with the exact Lévy sewing component already stored by that record.

It is still explicitly current-strength, not the final 2D acceptance proposition. Construction of an
embedded compact-surface presentation, Sengupta Facts 2--3, and all component inhabitants remain
open. The required compact-simple gauge geometry derives semisimplicity and discharges Theorem 8.4's
first source alternative.
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
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
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

/-- Current-strength joined record augmented by the exact Sengupta interfaces constructed so far. -/
structure TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData where
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

namespace TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData

omit [T2Space CoverGroup] [Fintype CurveS] [Nonempty CurveS] [DecidableEq EdgeS]
    [DecidableEq InternalEdge] in
/-- Exact literature-only inhabitance audit for the augmented record. It requires an inhabitant of
the prior current-strength join, one finite Sengupta law, its dependently indexed heat-factor bridge,
and its dependently indexed coherence with the exact Lévy sewing field. -/
theorem nonempty_iff_components :
    Nonempty (TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)) ↔
    ∃ _ : Geometry.CompactSimpleGaugeGroupData G E,
    ∃ current : TwoDimensionalCurrentStrengthLiteratureAcceptanceData
        (law := law) (inner := inner) (realLaplacian := realLaplacian)
        (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
        (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
        (identification := identification) (IG := IG)
        (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
        (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample),
      ∃ finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
          (G := G) (CoverGroup := CoverGroup) (Curve := CurveS) (Edge := EdgeS)
          (Region := RegionS) (Sample := SenguptaSample),
        Nonempty (TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
          (planarSemigroup := current.planar.convergence.productBridge.weakLimitFamily.spectralWilson
            |>.spectralHeatKernel.convolutionSemigroup)
          (finiteLaw := finiteLaw) (coverDensity := coverDensity)
          (InternalEdge := InternalEdge) (Face := FaceS)) ∧
        Nonempty (TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData
          finiteLaw current.compactSurface.sewing) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.gaugeGeometry, data.current, data.finiteLaw,
      ⟨data.heatFactors⟩, ⟨data.finiteLawSewing⟩⟩
  · rintro ⟨gaugeGeometry, current, finiteLaw, ⟨heatFactors⟩, ⟨finiteLawSewing⟩⟩
    exact ⟨⟨gaugeGeometry, current, finiteLaw, heatFactors, finiteLawSewing⟩⟩

omit [T2Space CoverGroup] [Fintype CurveS] [Nonempty CurveS] [DecidableEq EdgeS]
    [DecidableEq InternalEdge] in
/-- The stronger compact-simple gauge geometry discharges Sengupta Theorem 8.4's semisimple case by
Mathlib's simple-to-semisimple Lie-algebra theorem. -/
theorem sengupta_semisimple_source_hypothesis
    (data : TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)) :
    Geometry.HasSemisimpleGroupLieAlgebra G E :=
  Geometry.hasSemisimpleGroupLieAlgebra_of_hasSimple data.gaugeGeometry.simple_lieAlgebra

omit [T2Space CoverGroup] [Fintype CurveS] [Nonempty CurveS] [DecidableEq EdgeS] in
/-- Hostile dependency surface: the stored heat-factor bridge is indexed by this record's exact
finite law and exact nested planar spectral semigroup. -/
noncomputable def exact_heatFactors
    (data : TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)) :
    TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
      (planarSemigroup := data.current.planar.convergence.productBridge.weakLimitFamily.spectralWilson
        |>.spectralHeatKernel.convolutionSemigroup)
      (finiteLaw := data.finiteLaw) (coverDensity := coverDensity)
      (InternalEdge := InternalEdge) (Face := FaceS) :=
  data.heatFactors

omit [T2Space CoverGroup] [Fintype CurveS] [Nonempty CurveS] [DecidableEq EdgeS] in
/-- Hostile dependency surface: the finite-law sewing bridge uses this record's exact finite law and
the exact Lévy sewing field already selected inside `current`. -/
noncomputable def exact_finiteLawSewing
    (data : TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)) :
    TwoDimensionalSenguptaLevyFiniteHolonomyBridgeData
      data.finiteLaw data.current.compactSurface.sewing :=
  data.finiteLawSewing

omit [T2Space CoverGroup] [Fintype CurveS] [Nonempty CurveS] [DecidableEq EdgeS]
    [DecidableEq InternalEdge] in
/-- The covering heat bridge uses the exact planar spectral semigroup already selected by the current
Driver/Brownian chain. -/
theorem exact_planarSemigroup
    (data : TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
      (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
      (identification := identification) (IG := IG)
      (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
      (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
      (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
      (SenguptaSample := SenguptaSample) (coverDensity := coverDensity))
    {t : ℝ} (ht : 0 < t) :
    Measure.map data.finiteLaw.projection
        (normalizedCompactHaarDensitySemigroupMeasure coverDensity t) =
      normalizedCompactHaarDensitySemigroupMeasure law.selectedAreaDensity t :=
  data.heatFactors.coveringHeat.map_coverMeasure ht

end TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData

/-- Exact join of the prior augmented planar/Lévy/Sengupta record with the strongest current
embedded-universal compact finite-law record. It remains explicitly nonfinal. -/
structure TwoDimensionalSenguptaEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData where
  augmented : TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData
    (law := law) (inner := inner) (realLaplacian := realLaplacian)
    (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData)
    (continuum := continuum) (faceGeometry := faceGeometry) (Ω := Ω)
    (identification := identification) (IG := IG)
    (LeftLoop := LeftLoop) (RightLoop := RightLoop) (WholeLoop := WholeLoop)
    (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)
    (CoverGroup := CoverGroup) (CurveS := CurveS) (EdgeS := EdgeS)
    (InternalEdge := InternalEdge) (FaceS := FaceS) (RegionS := RegionS)
    (SenguptaSample := SenguptaSample) (coverDensity := coverDensity)
  compactFiniteLaw : TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
    (planarSemigroup := augmented.current.planar.convergence.productBridge.weakLimitFamily
      |>.spectralWilson.spectralHeatKernel.convolutionSemigroup)
    (finiteLaw := augmented.finiteLaw) (coverDensity := coverDensity)
    (heatFactors := augmented.heatFactors) (Surface := SenguptaSurface)
    (BaseVertex := SenguptaBaseVertex) (FineVertex := SenguptaFineVertex)
    (fine := senguptaFine) (TargetVertex := SenguptaTargetVertex)
    (target := senguptaTarget) (TargetSurface := SenguptaTargetSurface)

namespace TwoDimensionalSenguptaEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData

omit [T2Space CoverGroup] [Nonempty CurveS] [Fintype SenguptaTargetEdge] in
/-- Exact logical audit: the stronger wrapper needs the prior augmented witness and one compact
finite-law witness dependently indexed by its exact fields. -/
theorem nonempty_iff_components :
    Nonempty (TwoDimensionalSenguptaEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData
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
      (SenguptaTargetSurface := SenguptaTargetSurface)) ↔
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
      Nonempty (TwoDimensionalSenguptaEmbeddedUniversalFiniteLawAcceptanceData
        (planarSemigroup := augmented.current.planar.convergence.productBridge.weakLimitFamily
          |>.spectralWilson.spectralHeatKernel.convolutionSemigroup)
        (finiteLaw := augmented.finiteLaw) (coverDensity := coverDensity)
        (heatFactors := augmented.heatFactors) (Surface := SenguptaSurface)
        (BaseVertex := SenguptaBaseVertex) (FineVertex := SenguptaFineVertex)
        (fine := senguptaFine) (TargetVertex := SenguptaTargetVertex)
        (target := senguptaTarget) (TargetSurface := SenguptaTargetSurface)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.augmented, ⟨data.compactFiniteLaw⟩⟩
  · rintro ⟨augmented, ⟨compactFiniteLaw⟩⟩
    exact ⟨⟨augmented, compactFiniteLaw⟩⟩

end TwoDimensionalSenguptaEmbeddedUniversalAugmentedCurrentStrengthAcceptanceData

end

end YangMills.Dimensions
