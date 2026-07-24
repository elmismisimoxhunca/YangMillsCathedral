/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLaw

/-!
# Universal general-homeomorphism finite-curve law

This module states a fixed-universe, nonvacuous universal acceptance target for Sengupta Fact 3 at
the complete finite-curve-law level. Every general outer homeomorphism candidate must receive its own
preliminary source/target subdivisions, analytic transport chain, and target stochastic-law
representation, all tied to one unchanged source finite-holonomy law and covering density.

The record is uninhabited. It is not an unrestricted-universe Fact 3 theorem and constructs no
subdivision, measure, or four-dimensional Yang--Mills object.
-/

namespace YangMills.Dimensions

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

/-- The complete preliminary-subdivision and stochastic-law certificate selected for one general
outer candidate. The target normalizer is candidate-dependent. -/
structure TwoDimensionalSenguptaGeneralHomeomorphismFiniteCurveLawCandidateData
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) where
  targetPartitionFunction : ℝ≥0∞
  preliminaryGeometry :
    TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex} candidate
  stochastic : TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData sourceLaw
    candidate preliminaryGeometry coverDensity targetPartitionFunction

/-- Fixed-universe universal general-homeomorphism finite-curve-law acceptance. Candidate
nonemptiness prevents vacuous universal quantification. -/
structure TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData where
  candidate_nonempty : Nonempty
    (TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
  certificate_for : ∀ candidate :
    TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded),
    TwoDimensionalSenguptaGeneralHomeomorphismFiniteCurveLawCandidateData.{uG, uCover,
      uSample, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex,
      uSourceFineEdge, uSourceFineInternal, uSourceFineFace, uSourceFineVertex,
      uTargetFineEdge, uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (sourceLaw := sourceLaw) (coverDensity := coverDensity) candidate

namespace TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData

/-- Forget analytic and stochastic certification to the exact nonvacuous universal preliminary
subdivision geometry target. -/
noncomputable def toUniversalPreliminarySubdivisionGeometry
    (data : TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData.{uG, uCover,
      uSample, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex,
      uSourceFineEdge, uSourceFineInternal, uSourceFineFace, uSourceFineVertex,
      uTargetFineEdge, uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded) (sourceLaw := sourceLaw) (coverDensity := coverDensity)) :
    TwoDimensionalSenguptaUniversalGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
      uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
      uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded) where
  candidate_nonempty := data.candidate_nonempty
  preliminarySubdivision candidate := ⟨(data.certificate_for candidate).preliminaryGeometry⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Forgetting retains the exact per-candidate preliminary geometry witness. -/
theorem toUniversalPreliminarySubdivisionGeometry_preliminarySubdivision
    (data : TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData.{uG, uCover,
      uSample, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex,
      uSourceFineEdge, uSourceFineInternal, uSourceFineFace, uSourceFineVertex,
      uTargetFineEdge, uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded) (sourceLaw := sourceLaw) (coverDensity := coverDensity))
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)) :
    (data.toUniversalPreliminarySubdivisionGeometry).preliminarySubdivision candidate =
      ⟨(data.certificate_for candidate).preliminaryGeometry⟩ :=
  rfl

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Every general candidate represents the unchanged source stochastic sample law on its target
presentation for every distinguished region. -/
theorem finiteDimensionalLaw_on_target
    (data : TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData.{uG, uCover,
      uSample, uCurve, uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge,
      uTargetInternal, uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex,
      uSourceFineEdge, uSourceFineInternal, uSourceFineFace, uSourceFineVertex,
      uTargetFineEdge, uTargetFineInternal, uTargetFineFace, uTargetFineVertex}
      (baseEmbedded := baseEmbedded) (sourceLaw := sourceLaw) (coverDensity := coverDensity))
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
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
  (data.certificate_for candidate).stochastic.finiteDimensionalLaw_on_target region

end TwoDimensionalSenguptaUniversalGeneralHomeomorphismFiniteCurveLawData

end

end YangMills.Dimensions
