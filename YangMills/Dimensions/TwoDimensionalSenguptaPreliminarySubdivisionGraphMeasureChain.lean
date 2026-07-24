/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometry
import YangMills.Dimensions.TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransport
import YangMills.Dimensions.TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransport

/-!
# Preliminary-subdivision graph-measure chain

This module assembles the three normalized weighted-measure stages needed after a general Sengupta
Fact 3 preliminary subdivision geometry has been supplied:

1. source fine graph to source coarse graph;
2. source fine graph to target fine graph through the cellwise homeomorphism;
3. target fine graph to target coarse graph.

The record is an uninhabited compatibility target. It neither constructs the preliminary
subdivisions nor proves the stagewise Haar/density integration obligations.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uCover uCurve uEdge uInternal uFace uRegion uSurface uVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetSurface uTargetVertex
  uSourceFineEdge uSourceFineInternal uSourceFineFace uSourceFineVertex
  uTargetFineEdge uTargetFineInternal uTargetFineFace uTargetFineVertex

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
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

/-- One coherent normalized graph-measure chain through supplied preliminary source and target
subdivisions and their supplied fine cellwise homeomorphism. The same density and source twist are
used throughout; the target stages use the orientation-transported central twist. -/
structure TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData
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
    (coverDensity : ℝ → CoverGroup → ℝ≥0∞) (sourceTwist : CoverGroup)
    (sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞)
    (distinguishedRegion : Region) where
  sourceSubdivisionTransport :
    TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData
      preliminaryGeometry.sourceSubdivision
      (coverDensity := coverDensity) (bundleClass := sourceTwist)
      (coarsePartitionFunction := sourceCoarsePartitionFunction)
      (distinguishedRegion := distinguishedRegion)
  fineCellwiseTransport :
    TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData
      (coverDensity := coverDensity) (bundleClass := sourceTwist)
      (geometry := preliminaryGeometry.fineCellwise)
  targetSubdivisionTransport :
    TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData
      preliminaryGeometry.targetSubdivision
      (coverDensity := coverDensity)
      (bundleClass := senguptaTransportedBundleClass
        preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
      (coarsePartitionFunction := targetCoarsePartitionFunction)
      (distinguishedRegion := preliminaryGeometry.fineCellwise.regionEquiv distinguishedRegion)
  sourceFinePartition_coherence :
    fineCellwiseTransport.sourcePartitionFunction =
      sourceSubdivisionTransport.graphMeasure.finePartitionFunction
  targetFinePartition_coherence :
    fineCellwiseTransport.targetPartitionFunction =
      targetSubdivisionTransport.graphMeasure.finePartitionFunction

namespace TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The common source-fine measure used by both the source subdivision and cellwise stages. -/
def sourceFineGraphMeasure
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion)
    (region : Region) : Measure (preliminaryGeometry.SourceFineEdge → CoverGroup) :=
  senguptaCompactSurfaceGraphMeasure
    data.sourceSubdivisionTransport.graphMeasure.finePartitionFunction sourceTwist region
    (senguptaTriangulatedRegionFactor preliminaryGeometry.sourceFine coverDensity)
    (senguptaTriangulatedTwistedRegionFactor preliminaryGeometry.sourceFine coverDensity)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The common target-fine measure used by the cellwise and target-subdivision stages. -/
def targetFineGraphMeasure
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion)
    (region : Region) : Measure (preliminaryGeometry.TargetFineEdge → CoverGroup) :=
  senguptaCompactSurfaceGraphMeasure
    data.targetSubdivisionTransport.graphMeasure.finePartitionFunction
    (senguptaTransportedBundleClass preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
    (preliminaryGeometry.fineCellwise.regionEquiv region)
    (senguptaTriangulatedRegionFactor preliminaryGeometry.targetFine coverDensity)
    (senguptaTriangulatedTwistedRegionFactor preliminaryGeometry.targetFine coverDensity)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The common source-fine measure pushes to the original coarse source graph. -/
theorem sourceFine_to_sourceCoarse
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion)
    (region : Region) :
    Measure.map (preliminaryGeometry.sourceCurveRefinement.graph.configurationMap (G := CoverGroup))
      (data.sourceFineGraphMeasure region) =
    senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
      (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
      (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) :=
  data.sourceSubdivisionTransport.exact_graphMeasure_pushforward region

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- The same source-fine measure pushes, through the fine cellwise transport and target refinement,
to the original coarse target graph. This is the exact three-stage common-resolution chain; it does
not construct any stage certificate. -/
theorem sourceFine_to_targetCoarse
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion)
    (region : Region) :
    Measure.map
        (preliminaryGeometry.targetCurveRefinement.graph.configurationMap (G := CoverGroup) ∘
          senguptaTransportExternalField
            preliminaryGeometry.fineCellwise.externalEdgeEquiv)
        (data.sourceFineGraphMeasure region) =
      senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
        (senguptaTransportedBundleClass preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
        (preliminaryGeometry.fineCellwise.regionEquiv region)
        (senguptaTriangulatedRegionFactor candidate.target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity) := by
  have cellwise := data.fineCellwiseTransport.graphMeasure_pushforward region
  rw [data.sourceFinePartition_coherence, data.targetFinePartition_coherence] at cellwise
  calc
    Measure.map
        (preliminaryGeometry.targetCurveRefinement.graph.configurationMap (G := CoverGroup) ∘
          senguptaTransportExternalField preliminaryGeometry.fineCellwise.externalEdgeEquiv)
        (data.sourceFineGraphMeasure region) =
      Measure.map (preliminaryGeometry.targetCurveRefinement.graph.configurationMap (G := CoverGroup))
        (Measure.map
          (senguptaTransportExternalField preliminaryGeometry.fineCellwise.externalEdgeEquiv)
          (data.sourceFineGraphMeasure region)) := by
            symm
            exact Measure.map_map
              preliminaryGeometry.targetCurveRefinement.graph.configurationMap_measurable
              data.fineCellwiseTransport.transport_measurable
    _ = Measure.map
        (preliminaryGeometry.targetCurveRefinement.graph.configurationMap (G := CoverGroup))
        (data.targetFineGraphMeasure region) := by
          exact congrArg
            (Measure.map
              (preliminaryGeometry.targetCurveRefinement.graph.configurationMap
                (G := CoverGroup))) cellwise
    _ = senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
        (senguptaTransportedBundleClass preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
        (preliminaryGeometry.fineCellwise.regionEquiv region)
        (senguptaTriangulatedRegionFactor candidate.target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity) :=
      data.targetSubdivisionTransport.exact_graphMeasure_pushforward
        (preliminaryGeometry.fineCellwise.regionEquiv region)

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Every measurable group projection sends the two original coarse graph measures to the same
complete finite-curve holonomy law. This is a derived comparison through the common fine resolution,
not a supplied law equality and not yet a stochastic finite-law identification. -/
theorem coarse_projectedCurveHolonomy_law_eq
    {G : Type*} [Group G] [MeasurableSpace G]
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion)
    (projection : CoverGroup →* G) (projection_measurable : Measurable projection)
    (region : Region) :
    Measure.map (senguptaFiniteGraphHolonomy projection baseEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
          (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
          (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) =
      Measure.map (senguptaFiniteGraphHolonomy projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
          (senguptaTransportedBundleClass
            preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
          (preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) := by
  have sourceLaw := preliminaryGeometry.sourceCurveRefinement.map_projectedCurveHolonomy_eq
    projection projection_measurable (data.sourceFineGraphMeasure region)
    (senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
      (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
      (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity))
    (data.sourceFine_to_sourceCoarse region)
  rw [preliminaryGeometry.sourceSubdivision.fineCurveWord_eq_embedded] at sourceLaw
  have cellwiseLaw := data.fineCellwiseTransport.map_projectedCurveHolonomy_eq
    projection projection_measurable region
  rw [data.sourceFinePartition_coherence, data.targetFinePartition_coherence] at cellwiseLaw
  have targetLaw := preliminaryGeometry.targetCurveRefinement.map_projectedCurveHolonomy_eq
    projection projection_measurable (data.targetFineGraphMeasure region)
    (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
      (senguptaTransportedBundleClass preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
      (preliminaryGeometry.fineCellwise.regionEquiv region)
      (senguptaTriangulatedRegionFactor candidate.target coverDensity)
      (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity))
    (data.targetSubdivisionTransport.exact_graphMeasure_pushforward
      (preliminaryGeometry.fineCellwise.regionEquiv region))
  rw [preliminaryGeometry.targetSubdivision.fineCurveWord_eq_embedded] at targetLaw
  exact sourceLaw.trans (cellwiseLaw.symm.trans targetLaw.symm)

end TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData

/-- Projection-bearing source-facing endpoint for the preliminary-subdivision graph-measure chain.
It upgrades the formal projected-law comparison to one genuine covering projection and requires the
fixed central twist to lie in its kernel. It still does not identify either graph law with a
stochastic Yang--Mills sample law. -/
structure TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (chain : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion) where
  projection : CoverGroup →* G
  projection_isCoveringMap : IsCoveringMap projection
  projection_surjective : Function.Surjective projection
  projection_measurable : Measurable projection
  sourceTwist_mem_kernel : projection sourceTwist = 1

namespace TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The orientation-transported target twist remains in the same covering kernel. -/
theorem targetTwist_mem_kernel
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    {chain : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) chain) :
    data.projection (senguptaTransportedBundleClass
      preliminaryGeometry.fineCellwise.orientationSign sourceTwist) = 1 := by
  cases preliminaryGeometry.fineCellwise.orientationSign <;>
    simp [senguptaTransportedBundleClass, data.sourceTwist_mem_kernel]

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- The genuine covering projection gives equal complete finite-curve laws on the original source
and target coarse graphs. -/
theorem coarse_projectedCurveHolonomy_law_eq
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    {chain : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) chain)
    (region : Region) :
    Measure.map (senguptaFiniteGraphHolonomy data.projection baseEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
          (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
          (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) =
      Measure.map (senguptaFiniteGraphHolonomy data.projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
          (senguptaTransportedBundleClass
            preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
          (preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) :=
  chain.coarse_projectedCurveHolonomy_law_eq
    data.projection data.projection_measurable region

end TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData

end

end YangMills.Dimensions
