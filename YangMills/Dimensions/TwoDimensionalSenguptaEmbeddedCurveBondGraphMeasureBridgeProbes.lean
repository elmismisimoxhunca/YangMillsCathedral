/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridge

/-! Hostile probes for the embedded split-curve-bond graph-measure bridge. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridge.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff BigOperators

noncomputable section

variable
    {G Gauge Sample Connection CoverGroup Curve Edge InternalEdge Face Region SenguptaSample
      Surface BaseVertex SelectedFineInternal SelectedFineFace SelectedFineVertex
      TargetEdge TargetInternal TargetFace TargetRegion TargetVertex
      FineEdge FineInternal FineFace FineVertex : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {planarSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    [Group CoverGroup] [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup] [MeasurableSpace CoverGroup]
    [BorelSpace CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve]
    [Fintype Edge] [DecidableEq Edge]
    [Fintype InternalEdge] [DecidableEq InternalEdge]
    [Fintype Face] [DecidableEq Face]
    [Fintype Region] [DecidableEq Region]
    [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {heatFactors : TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity) (InternalEdge := InternalEdge) (Face := Face)}
    [TopologicalSpace Surface] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    [Fintype SelectedFineInternal] [DecidableEq SelectedFineInternal]
    [Fintype SelectedFineFace] [DecidableEq SelectedFineFace]
    {selectedFine : TwoDimensionalSenguptaTriangulatedRegionData
      Edge SelectedFineInternal SelectedFineFace Region}
    [Fintype TargetEdge] [DecidableEq TargetEdge]
    [Fintype TargetInternal] [DecidableEq TargetInternal]
    [Fintype TargetFace] [DecidableEq TargetFace] [DecidableEq TargetRegion]
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := SelectedFineVertex) (fine := selectedFine)
      (TargetVertex := TargetVertex) (target := target)}
    [Fintype FineEdge] [DecidableEq FineEdge]
    [Fintype FineInternal] [DecidableEq FineInternal]
    [Fintype FineFace] [DecidableEq FineFace]
    {fine : TwoDimensionalSenguptaTriangulatedRegionData FineEdge FineInternal FineFace Region}
    {fineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := FineVertex) fine}
    {fineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := fineClosed)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    {graphRefinement : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := finiteLaw)
      (coarseSource := fun edge => embeddedFiniteLaw.closedInvariance.baseClosed.edgeInitial
        (Sum.inl edge : Sum Edge InternalEdge))
      (coarseTarget := fun edge => embeddedFiniteLaw.closedInvariance.baseClosed.edgeTerminal
        (Sum.inl edge : Sum Edge InternalEdge))
      (fineSource := fun edge => fineClosed.edgeInitial
        (Sum.inl edge : Sum FineEdge FineInternal))
      (fineTarget := fun edge => fineClosed.edgeTerminal
        (Sum.inl edge : Sum FineEdge FineInternal))
      (fineCurveWord := fineCurveWord)}
    (data : TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (fine := fine) (fineClosed := fineClosed)
      (fineEmbedded := fineEmbedded) (graphRefinement := graphRefinement))

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- Embedded curve words are exactly the graph-level substitutions. -/
theorem exact_embedded_curve_refinement (curve : Curve) :
    fineEmbedded.curveWord curve =
      refineOrientedWord graphRefinement.curveRefinement.graph.edgeWord
        (finiteLaw.curveWord curve) :=
  TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData.embeddedCurveWord_eq_refinement
    data curve

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- Both ordinary and fixed-twist fine graph weights are the exact triangulated heat factors. -/
theorem exact_fine_heat_factors (region : Region) (external : FineEdge → CoverGroup) :
    graphRefinement.fineOrdinaryRegionWeight region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external ∧
    graphRefinement.fineTwistedRegionWeight finiteLaw.bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor fine coverDensity
        finiteLaw.bundleClass region external :=
  ⟨TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData.fineOrdinaryRegionWeight_eq
      data region external,
    TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData.fineTwistedRegionWeight_eq
      data region external⟩

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- The same stochastic law is represented on the actual embedded fine curve words. -/
theorem exact_embedded_fine_law (region : Region) :
    Measure.map finiteLaw.sampleHolonomy finiteLaw.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy finiteLaw.projection fineEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure graphRefinement.finePartitionFunction
          finiteLaw.bundleClass region graphRefinement.fineOrdinaryRegionWeight
          graphRefinement.fineTwistedRegionWeight) :=
  TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData.finiteDimensionalLaw_on_embeddedFineGraph
    data region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Hostile path probe: the graph edge word cannot be disconnected from its embedded total-edge word. -/
theorem changed_external_edge_word_blocked (edge : Edge)
    (changed : data.coarseEdgeToFineWord (Sum.inl edge) ≠
      (graphRefinement.curveRefinement.graph.edgeWord edge).map
        senguptaIncludeExternalOrientedEdge) : False :=
  changed (data.externalEdgeWord_coherence edge)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
include data in
/-- Hostile factor probe: changing the fixed fine ordinary heat factor is rejected. -/
theorem changed_fine_heat_factor_blocked (region : Region) (external : FineEdge → CoverGroup)
    (changed : graphRefinement.fineOrdinaryRegionWeight region external ≠
      senguptaTriangulatedRegionFactor fine coverDensity region external) : False :=
  changed
    (TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData.fineOrdinaryRegionWeight_eq
      data region external)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- Hostile signed-boundary probe: internal cancellation cannot be replaced by another chain. -/
theorem changed_signed_boundary_blocked (coarseFace : Face)
    (fineEdge : Sum FineEdge FineInternal)
    (changed : senguptaOrientedWordSignedIncidence fineEdge
        (senguptaSubstituteOrientedWord data.coarseEdgeToFineWord
          (heatFactors.triangulation.boundaryWord coarseFace)) ≠
      ∑ fineFace ∈ Finset.univ.filter (fun fineFace =>
          data.fineFaceToCoarse fineFace = coarseFace),
        senguptaOrientedWordSignedIncidence fineEdge (fine.boundaryWord fineFace)) : False :=
  changed (data.coarseFaceBoundary_signedChain_eq coarseFace fineEdge)

end

end YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridge.Probes
