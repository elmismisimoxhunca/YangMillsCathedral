/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChain

/-! Hostile probes for the general preliminary-subdivision graph-measure chain. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChain.Probes

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

variable
    {candidate : TwoDimensionalSenguptaGeneralEmbeddedHomeomorphismCandidateData.{uCurve,
      uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
      uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex}
      (baseEmbedded := baseEmbedded)}
    {preliminaryGeometry :
      TwoDimensionalSenguptaGeneralHomeomorphismPreliminarySubdivisionGeometryData.{uCurve,
        uEdge, uInternal, uFace, uRegion, uSurface, uVertex, uTargetEdge, uTargetInternal,
        uTargetFace, uTargetRegion, uTargetSurface, uTargetVertex, uSourceFineEdge,
        uSourceFineInternal, uSourceFineFace, uSourceFineVertex, uTargetFineEdge,
        uTargetFineInternal, uTargetFineFace, uTargetFineVertex} candidate}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞} {sourceTwist : CoverGroup}
    {sourceCoarsePartitionFunction targetCoarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChainData candidate
      preliminaryGeometry coverDensity sourceTwist sourceCoarsePartitionFunction
      targetCoarsePartitionFunction distinguishedRegion)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Exact positive probe: the common source-fine resolution recovers the original source graph. -/
theorem exact_source_leg (region : Region) :
    Measure.map
        (preliminaryGeometry.sourceCurveRefinement.graph.configurationMap (G := CoverGroup))
        (data.sourceFineGraphMeasure region) =
      senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) :=
  data.sourceFine_to_sourceCoarse region

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Exact positive probe: that same source-fine resolution reaches the original target graph through
the cellwise edge equivalence and target refinement. -/
theorem exact_target_leg (region : Region) :
    Measure.map
        (preliminaryGeometry.targetCurveRefinement.graph.configurationMap (G := CoverGroup) ∘
          senguptaTransportExternalField preliminaryGeometry.fineCellwise.externalEdgeEquiv)
        (data.sourceFineGraphMeasure region) =
      senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
        (senguptaTransportedBundleClass preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
        (preliminaryGeometry.fineCellwise.regionEquiv region)
        (senguptaTriangulatedRegionFactor candidate.target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity) :=
  data.sourceFine_to_targetCoarse region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile stage probe: the source subdivision transport cannot be omitted. -/
theorem missing_source_subdivision_transport_blocked
    (missing : ¬Nonempty
      (TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData
        preliminaryGeometry.sourceSubdivision
        (coverDensity := coverDensity) (bundleClass := sourceTwist)
        (coarsePartitionFunction := sourceCoarsePartitionFunction)
        (distinguishedRegion := distinguishedRegion))) : False :=
  missing ⟨data.sourceSubdivisionTransport⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile stage probe: the fine cellwise transport cannot be omitted. -/
theorem missing_fine_cellwise_transport_blocked
    (missing : ¬Nonempty
      (TwoDimensionalSenguptaParameterizedCellwiseGraphMeasureTransportData
        (coverDensity := coverDensity) (bundleClass := sourceTwist)
        (geometry := preliminaryGeometry.fineCellwise))) : False :=
  missing ⟨data.fineCellwiseTransport⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile stage probe: the target subdivision transport with the exact transported twist cannot
be omitted. -/
theorem missing_target_subdivision_transport_blocked
    (missing : ¬Nonempty
      (TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData
        preliminaryGeometry.targetSubdivision
        (coverDensity := coverDensity)
        (bundleClass := senguptaTransportedBundleClass
          preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
        (coarsePartitionFunction := targetCoarsePartitionFunction)
        (distinguishedRegion := preliminaryGeometry.fineCellwise.regionEquiv distinguishedRegion))) :
    False :=
  missing ⟨data.targetSubdivisionTransport⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile partition probe: disconnecting the cellwise source normalizer from the source
subdivision fine normalizer is rejected. -/
theorem changed_source_fine_partition_blocked
    (changed : data.fineCellwiseTransport.sourcePartitionFunction ≠
      data.sourceSubdivisionTransport.graphMeasure.finePartitionFunction) : False :=
  changed data.sourceFinePartition_coherence

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile partition probe: disconnecting the cellwise target normalizer from the target
subdivision fine normalizer is rejected. -/
theorem changed_target_fine_partition_blocked
    (changed : data.fineCellwiseTransport.targetPartitionFunction ≠
      data.targetSubdivisionTransport.graphMeasure.finePartitionFunction) : False :=
  changed data.targetFinePartition_coherence

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Hostile chain probe: changing the exact composite source-fine-to-target-coarse pushforward is
rejected. -/
theorem changed_target_leg_blocked (region : Region)
    (changed : Measure.map
        (preliminaryGeometry.targetCurveRefinement.graph.configurationMap (G := CoverGroup) ∘
          senguptaTransportExternalField preliminaryGeometry.fineCellwise.externalEdgeEquiv)
        (data.sourceFineGraphMeasure region) ≠
      senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
        (senguptaTransportedBundleClass preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
        (preliminaryGeometry.fineCellwise.regionEquiv region)
        (senguptaTriangulatedRegionFactor candidate.target coverDensity)
        (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) : False :=
  changed (data.sourceFine_to_targetCoarse region)

omit [T2Space CoverGroup] [Nonempty Curve] in
include data in
/-- Exact projected-law endpoint: both original coarse graph measures induce the same complete
finite-curve law under every measurable group projection. -/
theorem exact_coarse_projected_curve_law
    {G : Type*} [Group G] [MeasurableSpace G]
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
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) :=
  data.coarse_projectedCurveHolonomy_law_eq projection projection_measurable region

omit [T2Space CoverGroup] [Nonempty Curve] in
include data in
/-- Hostile projected-law probe: an altered coarse finite-curve law cannot pass through the common
fine resolution. -/
theorem changed_coarse_projected_curve_law_blocked
    {G : Type*} [Group G] [MeasurableSpace G]
    (projection : CoverGroup →* G) (projection_measurable : Measurable projection)
    (region : Region)
    (changed : Measure.map (senguptaFiniteGraphHolonomy projection baseEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
          (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
          (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) ≠
      Measure.map (senguptaFiniteGraphHolonomy projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
          (senguptaTransportedBundleClass
            preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
          (preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity))) : False :=
  changed (data.coarse_projectedCurveHolonomy_law_eq projection projection_measurable region)

omit [T2Space CoverGroup] [Nonempty Curve] in
/-- Projection-bearing positive probe: a genuine covering projection retains both kernel twists and
the derived coarse finite-curve law. -/
theorem exact_covering_projected_curve_law
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (projected : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) data)
    (region : Region) :
    IsCoveringMap projected.projection ∧
      Function.Surjective projected.projection ∧
      Measurable projected.projection ∧
      projected.projection sourceTwist = 1 ∧
      projected.projection (senguptaTransportedBundleClass
        preliminaryGeometry.fineCellwise.orientationSign sourceTwist) = 1 ∧
      Measure.map (senguptaFiniteGraphHolonomy projected.projection baseEmbedded.curveWord)
          (senguptaCompactSurfaceGraphMeasure sourceCoarsePartitionFunction sourceTwist region
            (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
            (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity)) =
        Measure.map
          (senguptaFiniteGraphHolonomy projected.projection candidate.targetEmbedded.curveWord)
          (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
            (senguptaTransportedBundleClass
              preliminaryGeometry.fineCellwise.orientationSign sourceTwist)
            (preliminaryGeometry.fineCellwise.regionEquiv region)
            (senguptaTriangulatedRegionFactor candidate.target coverDensity)
            (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) :=
  ⟨projected.projection_isCoveringMap, projected.projection_surjective,
    projected.projection_measurable, projected.sourceTwist_mem_kernel,
    projected.targetTwist_mem_kernel, projected.coarse_projectedCurveHolonomy_law_eq region⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile covering probe: an outside-kernel source twist cannot enter the projection-bearing
endpoint. -/
theorem outside_kernel_source_twist_blocked
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (projected : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) data)
    (outside : projected.projection sourceTwist ≠ 1) : False :=
  outside projected.sourceTwist_mem_kernel

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile covering probe: a non-covering projection cannot inhabit the source-facing endpoint. -/
theorem noncovering_projection_blocked
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (projected : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) data)
    (noncovering : ¬IsCoveringMap projected.projection) : False :=
  noncovering projected.projection_isCoveringMap

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile covering probe: a nonsurjective covering map cannot inhabit the source-facing
endpoint. -/
theorem nonsurjective_projection_blocked
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (projected : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) data)
    (nonsurjective : ¬Function.Surjective projected.projection) : False :=
  nonsurjective projected.projection_surjective

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile projection probe: topological covering data cannot replace the independently required
measurability into the physical target sigma-algebra. -/
theorem nonmeasurable_projection_blocked
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (projected : TwoDimensionalSenguptaPreliminarySubdivisionProjectedFiniteCurveLawData
      (G := G) data)
    (nonmeasurable : ¬Measurable projected.projection) : False :=
  nonmeasurable projected.projection_measurable

end

end YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionGraphMeasureChain.Probes
