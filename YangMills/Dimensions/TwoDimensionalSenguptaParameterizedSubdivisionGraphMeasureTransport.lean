/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedCurveBondGraphMeasureBridge
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinement

/-!
# Parameterized subdivision graph-measure transport

This module attaches the reusable parameterized weighted graph-measure refinement to one exact
parameterized embedded split-bond subdivision geometry. Both coarse and fine weights are required to
be the boundary-conditioned factors of one normalized covering density semigroup. No convolution
integration proof or subdivision construction is supplied.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uCover uCurve uCoarseEdge uCoarseInternal uCoarseFace uCoarseRegion
  uCoarseVertex uCoarseSurface uFineEdge uFineInternal uFineFace uFineVertex

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {CoarseEdge : Type uCoarseEdge} [Fintype CoarseEdge] [DecidableEq CoarseEdge]
    {CoarseInternal : Type uCoarseInternal} [Fintype CoarseInternal]
    [DecidableEq CoarseInternal]
    {CoarseFace : Type uCoarseFace} [Fintype CoarseFace] [DecidableEq CoarseFace]
    {CoarseRegion : Type uCoarseRegion} [Fintype CoarseRegion] [DecidableEq CoarseRegion]
    {CoarseVertex : Type uCoarseVertex}
    {CoarseSurface : Type uCoarseSurface} [TopologicalSpace CoarseSurface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) CoarseSurface]
    {coarse : TwoDimensionalSenguptaTriangulatedRegionData
      CoarseEdge CoarseInternal CoarseFace CoarseRegion}
    {coarseClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := CoarseVertex) coarse}
    {coarseEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := CoarseSurface) (Curve := Curve) (closed := coarseClosed)}
    {coarseCurveWord : Curve → List (OrientedEdge CoarseEdge)}
    {FineEdge : Type uFineEdge} [Fintype FineEdge] [DecidableEq FineEdge]
    {FineInternal : Type uFineInternal} [Fintype FineInternal] [DecidableEq FineInternal]
    {FineFace : Type uFineFace} [Fintype FineFace] [DecidableEq FineFace]
    {FineVertex : Type uFineVertex}
    {fine : TwoDimensionalSenguptaTriangulatedRegionData
      FineEdge FineInternal FineFace CoarseRegion}
    {fineClosed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := FineVertex) fine}
    {fineEmbedded : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := CoarseSurface) (Curve := Curve) (closed := fineClosed)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    {curveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
      (coarseSource := fun edge => coarseClosed.edgeInitial (Sum.inl edge))
      (coarseTarget := fun edge => coarseClosed.edgeTerminal (Sum.inl edge))
      (fineSource := fun edge => fineClosed.edgeInitial (Sum.inl edge))
      (fineTarget := fun edge => fineClosed.edgeTerminal (Sum.inl edge))
      (coarseCurveWord := coarseCurveWord) (fineCurveWord := fineCurveWord)}
    {geometry : TwoDimensionalSenguptaParameterizedEmbeddedCurveBondSubdivisionGeometryData
      coarse coarseClosed coarseEmbedded coarseCurveWord fine fineClosed fineEmbedded fineCurveWord
      curveRefinement}
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {bundleClass : CoverGroup}
    {coarsePartitionFunction : ℝ≥0∞}
    {distinguishedRegion : CoarseRegion}

/-- Exact normalized density-semigroup graph-measure certificate attached to one supplied embedded
subdivision geometry. The generic weighted refinement is retained, but its curve refinement and fine
weights must be exactly those selected by the geometry and fine triangulation. The fixed twist is
central. This projection-free layer deliberately leaves kernel membership to an outer finite-law
certificate carrying the covering projection. -/
structure TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData
    (geometry : TwoDimensionalSenguptaParameterizedEmbeddedCurveBondSubdivisionGeometryData
      coarse coarseClosed coarseEmbedded coarseCurveWord fine fineClosed fineEmbedded fineCurveWord
      curveRefinement) where
  coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity
  bundleClass_central : ∀ element, bundleClass * element = element * bundleClass
  graphMeasure : TwoDimensionalSenguptaParameterizedCurveBondGraphMeasureRefinementData
    (coarseSource := fun edge => coarseClosed.edgeInitial (Sum.inl edge))
    (coarseTarget := fun edge => coarseClosed.edgeTerminal (Sum.inl edge))
    (fineSource := fun edge => fineClosed.edgeInitial (Sum.inl edge))
    (fineTarget := fun edge => fineClosed.edgeTerminal (Sum.inl edge))
    coarseCurveWord bundleClass
    (senguptaTriangulatedRegionFactor coarse coverDensity)
    (senguptaTriangulatedTwistedRegionFactor coarse coverDensity)
    coarsePartitionFunction distinguishedRegion fineCurveWord
  curveRefinement_eq : graphMeasure.curveRefinement = curveRefinement
  fineOrdinaryRegionWeight_eq : ∀ region external,
    graphMeasure.fineOrdinaryRegionWeight region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external
  fineTwistedRegionWeight_eq : ∀ region external,
    graphMeasure.fineTwistedRegionWeight bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor fine coverDensity bundleClass region external

namespace TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- The stored generic pushforward is exactly the geometric refinement pushforward between the
coarse and fine normalized density-semigroup factor measures. -/
theorem exact_graphMeasure_pushforward
    (data : TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData
      (geometry := geometry) (coverDensity := coverDensity) (bundleClass := bundleClass)
      (coarsePartitionFunction := coarsePartitionFunction)
      (distinguishedRegion := distinguishedRegion))
    (region : CoarseRegion) :
    Measure.map (curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure data.graphMeasure.finePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor fine coverDensity)
        (senguptaTriangulatedTwistedRegionFactor fine coverDensity)) =
    senguptaCompactSurfaceGraphMeasure coarsePartitionFunction bundleClass region
      (senguptaTriangulatedRegionFactor coarse coverDensity)
      (senguptaTriangulatedTwistedRegionFactor coarse coverDensity) := by
  have ordinaryEq : data.graphMeasure.fineOrdinaryRegionWeight =
      senguptaTriangulatedRegionFactor fine coverDensity := by
    funext selectedRegion external
    exact data.fineOrdinaryRegionWeight_eq selectedRegion external
  have fineMeasureEq :
      senguptaCompactSurfaceGraphMeasure data.graphMeasure.finePartitionFunction bundleClass region
          data.graphMeasure.fineOrdinaryRegionWeight data.graphMeasure.fineTwistedRegionWeight =
        senguptaCompactSurfaceGraphMeasure data.graphMeasure.finePartitionFunction bundleClass region
          (senguptaTriangulatedRegionFactor fine coverDensity)
          (senguptaTriangulatedTwistedRegionFactor fine coverDensity) := by
    unfold senguptaCompactSurfaceGraphMeasure senguptaCompactSurfaceGraphWeight
    congr 1
    funext field
    rw [data.fineTwistedRegionWeight_eq, ordinaryEq]
  have pushforward := data.graphMeasure.graphMeasure_pushforward region
  rw [data.curveRefinement_eq, fineMeasureEq] at pushforward
  exact pushforward

end TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData

end

end YangMills.Dimensions
