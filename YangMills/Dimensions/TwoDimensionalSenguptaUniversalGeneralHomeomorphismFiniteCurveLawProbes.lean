/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLaw

/-! Hostile probes for universal general-homeomorphism finite-curve-law acceptance. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLaw.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uG uCover uSample uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex
  uSourceFineEdge uSourceFineInternal uSourceFineFace uSourceFineVertex
  uTargetFineEdge uTargetFineInternal uTargetFineFace uTargetFineVertex

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge] [DecidableEq InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {Vertex : Type uVertex}
    {baseTriangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {baseClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) baseTriangulation}
    {baseEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := baseClosed)}
    {sourceLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    (data : TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData.{uG, uCover,
      uSample, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex,
      uSourceFineEdge, uSourceFineInternal, uSourceFineFace, uSourceFineVertex,
      uTargetFineEdge, uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded) (sourceLaw := sourceLaw) (coverDensity := coverDensity))

attribute [local instance]
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetSurfaceTopology
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetSurfaceCharted
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetEdgeFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetEdgeDecidableEq
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetInternalFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetInternalDecidableEq
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetFaceFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetFaceDecidableEq
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetRegionFintype
  TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.targetRegionDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineEdgeFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineEdgeDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineInternalFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineInternalDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineFaceFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.sourceFineFaceDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineEdgeFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineEdgeDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineInternalFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineInternalDecidableEq
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineFaceFintype
  TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.targetFineFaceDecidableEq

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Candidate nonemptiness prevents an empty universal Fact 3 class. -/
theorem candidate_class_nonempty : Nonempty
    (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve, uEdge,
      uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) :=
  data.candidate_nonempty

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The universal stochastic endpoint forgets exactly to the prior universal geometry target. -/
theorem exact_universal_geometry :
    (data.toUniversalPreliminarySubdivisionGeometry).candidate_nonempty = data.candidate_nonempty ∧
    ∀ candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
        uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
        uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
        (baseEmbedded := baseEmbedded),
      (data.toUniversalPreliminarySubdivisionGeometry).preliminarySubdivision candidate =
        ⟨(data.certificate_for candidate).preliminaryGeometry⟩ :=
  ⟨rfl, data.toUniversalPreliminarySubdivisionGeometry_preliminarySubdivision⟩

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Every concrete general candidate receives the unchanged stochastic finite-curve law on its
target presentation. -/
theorem exact_target_law
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
    (region : Region) :
    Measure.map sourceLaw.sampleHolonomy sourceLaw.sampleMeasure =
      Measure.map
        (senguptaFiniteGraphHolonomy sourceLaw.projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure
          (data.certificate_for candidate).targetPartitionFunction
          (senguptaTransportedBundleClass
            (data.certificate_for candidate).preliminaryGeometry.fineCellwise.orientationSign
            sourceLaw.bundleClass)
          ((data.certificate_for candidate).preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) :=
  data.finiteDimensionalLaw_on_target candidate region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile universal probe: an empty candidate class cannot satisfy the record. -/
theorem empty_candidate_class_blocked
    (empty : ¬Nonempty
      (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve, uEdge,
        uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
        uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
        (baseEmbedded := baseEmbedded))) : False :=
  empty data.candidate_nonempty

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile candidate probe: no concrete candidate may omit its full geometric/analytic/stochastic
certificate. -/
theorem missing_candidate_certificate_blocked
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
    (missing : ¬Nonempty
      (TwoDimensionalSenguptaGeneralHomeomorphismFiniteCurveLawCandidateData.{uG, uCover,
        uSample, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex,
        uTargetEdge, uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface,
        uTargetVertex, uSourceFineEdge, uSourceFineInternal, uSourceFineFace,
        uSourceFineVertex, uTargetFineEdge, uTargetFineInternal, uTargetFineFace,
        uTargetFineVertex}
        (sourceLaw := sourceLaw) (coverDensity := coverDensity) candidate)) : False :=
  missing ⟨data.certificate_for candidate⟩

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Hostile law probe: changing any candidate's target finite-curve law is rejected. -/
theorem changed_target_law_blocked
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
    (region : Region)
    (changed : Measure.map sourceLaw.sampleHolonomy sourceLaw.sampleMeasure ≠
      Measure.map
        (senguptaFiniteGraphHolonomy sourceLaw.projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure
          (data.certificate_for candidate).targetPartitionFunction
          (senguptaTransportedBundleClass
            (data.certificate_for candidate).preliminaryGeometry.fineCellwise.orientationSign
            sourceLaw.bundleClass)
          ((data.certificate_for candidate).preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity))) : False :=
  changed (data.finiteDimensionalLaw_on_target candidate region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLaw.Probes
