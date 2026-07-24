/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinement
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedComparisonBridge

/-!
# Embedded split-curve-bond Sengupta graph-measure bridge

This file joins one exact split-curve-bond equation-(8.3) graph-measure refinement to actual
embedded coarse and fine triangular presentations on the same compact surface. The fine graph
weights are exactly the boundary-conditioned heat factors of the fine triangulation, every coarse
bond has a geometric fine-word realization, and coarse triangular boundaries equal the signed sum
of their fine boundaries after internal cancellation.

This is an uninhabited one-pair bridge. The weighted pushforward remains supplied by the underlying
refinement datum; no heat-kernel integration proof or universal Fact 2 is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal Manifold ContDiff BigOperators

noncomputable section

/-- Include a fine external oriented edge into the total fine triangulation edge carrier. -/
def senguptaIncludeExternalOrientedEdge
    {External Internal : Type*} : OrientedEdge External → OrientedEdge (Sum External Internal)
  | .forward edge => .forward (Sum.inl edge)
  | .reverse edge => .reverse (Sum.inl edge)

universe uG uCover uGauge uSample uConnection uCurve uEdge uInternal uFace uRegion
  uSenguptaSample uSurface uBaseVertex
  uSelectedFineInternal uSelectedFineFace uSelectedFineVertex
  uTargetEdge uTargetInternal uTargetFace uTargetRegion uTargetVertex
  uFineEdge uFineInternal uFineFace uFineVertex

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {planarSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
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
    {SenguptaSample : Type uSenguptaSample} [MeasurableSpace SenguptaSample]
    {finiteLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := Edge)
      (Region := Region) (Sample := SenguptaSample)}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {heatFactors : TwoDimensionalSenguptaTriangulatedHeatFactorBridgeData
      (planarSemigroup := planarSemigroup) (finiteLaw := finiteLaw)
      (coverDensity := coverDensity) (InternalEdge := InternalEdge) (Face := Face)}
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {BaseVertex : Type uBaseVertex}
    {SelectedFineInternal : Type uSelectedFineInternal}
      [Fintype SelectedFineInternal] [DecidableEq SelectedFineInternal]
    {SelectedFineFace : Type uSelectedFineFace}
      [Fintype SelectedFineFace] [DecidableEq SelectedFineFace]
    {SelectedFineVertex : Type uSelectedFineVertex}
    {selectedFine : TwoDimensionalSenguptaTriangulatedRegionData
      Edge SelectedFineInternal SelectedFineFace Region}
    {TargetEdge : Type uTargetEdge} [Fintype TargetEdge] [DecidableEq TargetEdge]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
      [DecidableEq TargetInternal]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {TargetVertex : Type uTargetVertex}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {embeddedFiniteLaw : TwoDimensionalSenguptaEmbeddedFiniteLawBridgeData
      (heatFactors := heatFactors) (Surface := Surface) (BaseVertex := BaseVertex)
      (FineVertex := SelectedFineVertex) (fine := selectedFine)
      (TargetVertex := TargetVertex) (target := target)}
    {FineEdge : Type uFineEdge} [Fintype FineEdge] [DecidableEq FineEdge]
    {FineInternal : Type uFineInternal} [Fintype FineInternal] [DecidableEq FineInternal]
    {FineFace : Type uFineFace} [Fintype FineFace] [DecidableEq FineFace]
    {FineVertex : Type uFineVertex}
    {fine : TwoDimensionalSenguptaTriangulatedRegionData FineEdge FineInternal FineFace Region}
    {fineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := FineVertex) fine}
    {fineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := fineClosed)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    {graphRefinement : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := finiteLaw)
      (coarseSource := fun edge =>
        embeddedFiniteLaw.closedInvariance.baseClosed.edgeInitial
          (Sum.inl edge : Sum Edge InternalEdge))
      (coarseTarget := fun edge =>
        embeddedFiniteLaw.closedInvariance.baseClosed.edgeTerminal
          (Sum.inl edge : Sum Edge InternalEdge))
      (fineSource := fun edge => fineClosed.edgeInitial (Sum.inl edge : Sum FineEdge FineInternal))
      (fineTarget := fun edge => fineClosed.edgeTerminal (Sum.inl edge : Sum FineEdge FineInternal))
      (fineCurveWord := fineCurveWord)}

/-- Geometric and heat-factor realization of one split-curve-bond weighted graph refinement. -/
structure TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData where
  fineCurveWord_eq_embedded : fineCurveWord = fineEmbedded.curveWord
  fineOrdinaryRegionWeight_eq : ∀ region external,
    graphRefinement.fineOrdinaryRegionWeight region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external
  fineTwistedRegionWeight_eq : ∀ region external,
    graphRefinement.fineTwistedRegionWeight finiteLaw.bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor fine coverDensity finiteLaw.bundleClass region external
  fineFaceToCoarse : FineFace → Face
  fineFaceToCoarse_surjective : Function.Surjective fineFaceToCoarse
  faceRegion_coherence : ∀ fineFace,
    heatFactors.triangulation.faceRegion (fineFaceToCoarse fineFace) = fine.faceRegion fineFace
  regionArea_coherence : ∀ region,
    heatFactors.triangulation.regionArea region = fine.regionArea region
  fineFaceImage_subset : ∀ fineFace,
    Set.range (fineEmbedded.faceDisk fineFace) ⊆
      Set.range (embeddedFiniteLaw.embeddedBase.faceDisk (fineFaceToCoarse fineFace))
  coarseFaceImage_eq_fine_union : ∀ coarseFace,
    Set.range (embeddedFiniteLaw.embeddedBase.faceDisk coarseFace) =
      ⋃ (fineFace : FineFace) (_ : fineFaceToCoarse fineFace = coarseFace),
        Set.range (fineEmbedded.faceDisk fineFace)
  baseVertexToFine : BaseVertex → FineVertex
  baseVertexToFine_injective : Function.Injective baseVertexToFine
  baseVertexToFine_point : ∀ vertex,
    fineEmbedded.vertexPoint (baseVertexToFine vertex) =
      embeddedFiniteLaw.embeddedBase.vertexPoint vertex
  coarseEdgeToFineWord : Sum Edge InternalEdge →
    List (OrientedEdge (Sum FineEdge FineInternal))
  externalEdgeWord_coherence : ∀ edge,
    coarseEdgeToFineWord (Sum.inl edge) =
      (graphRefinement.curveRefinement.graph.edgeWord edge).map
        senguptaIncludeExternalOrientedEdge
  coarseEdgeToFineWord_realizes : ∀ edge,
    IsSenguptaEmbeddedPathSubdivision embeddedFiniteLaw.embeddedBase.edgePath
      fineEmbedded.edgePath edge (coarseEdgeToFineWord edge)
  coarseFaceBoundary_signedChain_eq : ∀ (coarseFace : Face)
      (fineEdge : Sum FineEdge FineInternal),
    senguptaOrientedWordSignedIncidence fineEdge
      (senguptaSubstituteOrientedWord coarseEdgeToFineWord
        (heatFactors.triangulation.boundaryWord coarseFace)) =
    ∑ fineFace ∈ Finset.univ.filter (fun fineFace =>
        fineFaceToCoarse fineFace = coarseFace),
      senguptaOrientedWordSignedIncidence fineEdge (fine.boundaryWord fineFace)
  fineRegionSet_eq : ∀ region : Region,
    fineEmbedded.regionSet region = embeddedFiniteLaw.embeddedBase.regionSet region

namespace TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- The exact fine embedded curve words are the literal graph-refined coarse finite-law words. -/
theorem embeddedCurveWord_eq_refinement
    (data : TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (fine := fine) (fineClosed := fineClosed)
      (fineEmbedded := fineEmbedded) (graphRefinement := graphRefinement))
    (curve : Curve) :
    fineEmbedded.curveWord curve =
      refineOrientedWord graphRefinement.curveRefinement.graph.edgeWord
        (finiteLaw.curveWord curve) := by
  rw [← data.fineCurveWord_eq_embedded]
  exact graphRefinement.curveRefinement.curveWord_refinement curve

omit [T2Space CoverGroup] [Nonempty Curve] [Fintype TargetEdge] in
/-- The refined embedded graph carries the unchanged stochastic projected finite-curve law. -/
theorem finiteDimensionalLaw_on_embeddedFineGraph
    (data : TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (fine := fine) (fineClosed := fineClosed)
      (fineEmbedded := fineEmbedded) (graphRefinement := graphRefinement))
    (region : Region) :
    Measure.map finiteLaw.sampleHolonomy finiteLaw.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy finiteLaw.projection fineEmbedded.curveWord)
        (senguptaCompactSurfaceGraphMeasure graphRefinement.finePartitionFunction
          finiteLaw.bundleClass region graphRefinement.fineOrdinaryRegionWeight
          graphRefinement.fineTwistedRegionWeight) := by
  rw [← data.fineCurveWord_eq_embedded]
  exact graphRefinement.finiteDimensionalLaw_on_fineGraph region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] [Fintype TargetEdge] in
/-- The fine graph's ordinary region weights are exactly its boundary-conditioned heat factors. -/
theorem exact_fineOrdinaryRegionWeight
    (data : TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData
      (embeddedFiniteLaw := embeddedFiniteLaw) (fine := fine) (fineClosed := fineClosed)
      (fineEmbedded := fineEmbedded) (graphRefinement := graphRefinement))
    (region : Region) (external : FineEdge → CoverGroup) :
    graphRefinement.fineOrdinaryRegionWeight region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external :=
  data.fineOrdinaryRegionWeight_eq region external

end TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridgeData

end

end YangMills.Dimensions
