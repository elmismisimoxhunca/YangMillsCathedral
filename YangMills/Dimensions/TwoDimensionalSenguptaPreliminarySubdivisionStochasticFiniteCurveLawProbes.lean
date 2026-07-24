/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLaw

/-! Hostile probes for the stochastic preliminary-subdivision finite-curve law. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLaw.Probes

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

variable
    {sourceLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := Sample)}
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
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {targetCoarsePartitionFunction : ℝ≥0∞}
    (data : TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLawData sourceLaw
      candidate preliminaryGeometry coverDensity targetCoarsePartitionFunction)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Exact positive probe: the source finite law constructs the projection-bearing chain endpoint. -/
theorem exact_projected_endpoint :
    (data.toProjected).projection = sourceLaw.projection ∧
      IsCoveringMap (data.toProjected).projection ∧
      Function.Surjective (data.toProjected).projection ∧
      Measurable (data.toProjected).projection ∧
      (data.toProjected).projection sourceLaw.bundleClass = 1 :=
  ⟨rfl, sourceLaw.projection_isCoveringMap, sourceLaw.projection_surjective,
    data.projection_measurable, sourceLaw.bundleClass_mem_kernel⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Exact source endpoint probe: the finite-law graph measure is the chain's canonical source
measure. -/
theorem exact_source_graph_measure (region : Region) :
    senguptaCompactSurfaceGraphMeasure sourceLaw.partitionFunction sourceLaw.bundleClass region
        sourceLaw.ordinaryRegionWeight sourceLaw.twistedRegionWeight =
      senguptaCompactSurfaceGraphMeasure sourceLaw.partitionFunction sourceLaw.bundleClass region
        (senguptaTriangulatedRegionFactor baseTriangulation coverDensity)
        (senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity) :=
  data.sourceGraphMeasure_eq region

omit [T2Space CoverGroup] [Nonempty Curve] in
include data in
/-- Exact target endpoint: the unchanged stochastic sample law is represented on the target coarse
presentation for every distinguished-region choice. -/
theorem exact_target_finite_curve_law (region : Region) :
    Measure.map sourceLaw.sampleHolonomy sourceLaw.sampleMeasure =
      Measure.map
        (senguptaFiniteGraphHolonomy sourceLaw.projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
          (senguptaTransportedBundleClass
            preliminaryGeometry.fineCellwise.orientationSign sourceLaw.bundleClass)
          (preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity)) :=
  data.finiteDimensionalLaw_on_target region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile source probe: unrelated coarse curve words cannot be substituted. -/
theorem changed_source_curve_words_blocked
    (changed : sourceLaw.curveWord ≠ baseEmbedded.curveWord) : False :=
  changed data.sourceCurveWord_eq

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile source probe: changing any ordinary source factor is rejected. -/
theorem changed_source_ordinary_factor_blocked
    (changed : sourceLaw.ordinaryRegionWeight ≠
      senguptaTriangulatedRegionFactor baseTriangulation coverDensity) : False :=
  changed data.sourceOrdinaryRegionWeight_eq

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile source probe: changing the fixed source twist factor is rejected. -/
theorem changed_source_twisted_factor_blocked (region : Region)
    (external : Edge → CoverGroup)
    (changed : sourceLaw.twistedRegionWeight sourceLaw.bundleClass region external ≠
      senguptaTriangulatedTwistedRegionFactor baseTriangulation coverDensity
        sourceLaw.bundleClass region external) : False :=
  changed (data.sourceTwistedRegionWeight_eq region external)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile projection probe: source-law projection measurability cannot be omitted. -/
theorem nonmeasurable_source_projection_blocked
    (nonmeasurable : ¬Measurable sourceLaw.projection) : False :=
  nonmeasurable data.projection_measurable

omit [T2Space CoverGroup] [Nonempty Curve] in
include data in
/-- Hostile stochastic endpoint: changing the target representation of the unchanged sample law is
rejected. -/
theorem changed_target_finite_curve_law_blocked (region : Region)
    (changed : Measure.map sourceLaw.sampleHolonomy sourceLaw.sampleMeasure ≠
      Measure.map
        (senguptaFiniteGraphHolonomy sourceLaw.projection candidate.targetEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure targetCoarsePartitionFunction
          (senguptaTransportedBundleClass
            preliminaryGeometry.fineCellwise.orientationSign sourceLaw.bundleClass)
          (preliminaryGeometry.fineCellwise.regionEquiv region)
          (senguptaTriangulatedRegionFactor candidate.target coverDensity)
          (senguptaTriangulatedTwistedRegionFactor candidate.target coverDensity))) : False :=
  changed (data.finiteDimensionalLaw_on_target region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaPreliminarySubdivisionStochasticFiniteCurveLaw.Probes
