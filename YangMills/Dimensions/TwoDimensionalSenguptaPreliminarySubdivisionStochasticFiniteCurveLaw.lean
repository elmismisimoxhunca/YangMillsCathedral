/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChain

/-!
# Stochastic finite-curve law through preliminary subdivisions

This module identifies the source endpoint of a supplied preliminary-subdivision graph-measure chain
with one existing Sengupta finite-holonomy sample law. The already-derived common-resolution theorem
then transports that same complete finite-curve law to the target coarse presentation.

No sample law, subdivision, integration theorem, or full Fact 3 witness is constructed.
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

/-- One existing stochastic finite-holonomy law identified with the source endpoint of the exact
preliminary-subdivision graph-measure chain. -/
structure TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData
    (sourceLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample))
    (candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded))
    (preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
        uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
        uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
        uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
        uTargetFineInternal, uTargetFineFace, uTargetFineVertex} candidate)
    (coverDensity : ℝ → CoverGroup → ℝ≥0∞)
    (targetCoarsePartitionFunction : ℝ≥0∞) where
  chain : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
    preliminaryGeometry coverDensity sourceLaw.bundleClass sourceLaw.partitionFunction
    targetCoarsePartitionFunction sourceLaw.distinguishedRegion
  projection_measurable : Measurable sourceLaw.projection
  sourceCurveWord_eq : sourceLaw.curveWord = baseEmbedded.curveWord
  sourceOrdinaryRegionWeight_eq : sourceLaw.ordinaryRegionWeight =
    senguptaTriangulatedRegionFactor baseTriangulation coverDensity
  sourceTwistedRegionWeight_eq : ∀ region external,
    sourceLaw.twistedRegionWeight sourceLaw.bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity
        sourceLaw.bundleClass region external

namespace TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData

/-- The existing source finite law supplies the genuine projection-bearing endpoint required by the
common-resolution chain. -/
noncomputable def toProjected
    {sourceLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)}
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {targetCoarsePartitionFunction : ℝ≥0∞}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData sourceLaw
      candidate preliminaryGeometry coverDensity targetCoarsePartitionFunction) :
    TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) data.chain where
  projection := sourceLaw.projection
  projection_isCoveringMap := sourceLaw.projection_isCoveringMap
  projection_surjective := sourceLaw.projection_surjective
  projection_measurable := data.projection_measurable
  sourceTwist_mem_kernel := sourceLaw.bundleClass_mem_kernel

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The source law's graph measure is exactly the canonical source endpoint measure of the chain. -/
theorem sourceGraphMeasure_eq
    {sourceLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)}
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {targetCoarsePartitionFunction : ℝ≥0∞}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData sourceLaw
      candidate preliminaryGeometry coverDensity targetCoarsePartitionFunction)
    (region : Region) :
    senguptaCompactSurfaceGraphMeasure sourceLaw.partitionFunction sourceLaw.bundleClass region
        sourceLaw.ordinaryRegionWeight sourceLaw.twistedRegionWeight =
      senguptaCompactSurfaceGraphMeasure sourceLaw.partitionFunction sourceLaw.bundleClass region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) := by
  unfold senguptaCompactSurfaceGraphMeasure senguptaCompactSurfaceGraphWeight
  congr 1
  funext field
  rw [data.sourceTwistedRegionWeight_eq, data.sourceOrdinaryRegionWeight_eq]

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- The unchanged stochastic sample law is represented on the original target presentation after
the supplied preliminary-subdivision chain. -/
theorem finiteDimensionalLaw_on_target
    {sourceLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)}
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {targetCoarsePartitionFunction : ℝ≥0∞}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData sourceLaw
      candidate preliminaryGeometry coverDensity targetCoarsePartitionFunction)
    (region : Region) :
    Measure.map sourceLaw.sampleHolonomy sourceLaw.sampleMeasure =
      Measure.map
        (senguptaFiniteGraphHolonomy sourceLaw.projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
          (senguptaTransportedBundleClass
            preliminaryGeometry.fineCellwise.orientationSign sourceLaw.bundleClass)
          (preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) := by
  have sourceFiniteLaw := sourceLaw.finiteDimensionalLaw_atRegion region
  rw [data.sourceCurveWord_eq, data.sourceGraphMeasure_eq region] at sourceFiniteLaw
  exact sourceFiniteLaw.trans
    (data.toProjected.coarse_projectedCurveHolonomy_law_eq region)

end TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData

end

end YangMills.Dimensions
