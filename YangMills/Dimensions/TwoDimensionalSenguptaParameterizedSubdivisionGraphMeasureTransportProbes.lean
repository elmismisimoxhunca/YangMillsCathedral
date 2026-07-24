/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransport

/-! Hostile probes for parameterized subdivision graph-measure transport. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransport.Probes

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
    (data : TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransportData geometry
      (coverDensity := coverDensity) (bundleClass := bundleClass)
      (coarsePartitionFunction := coarsePartitionFunction)
      (distinguishedRegion := distinguishedRegion))

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Exact positive probe: the fine normalized density-semigroup measure pushes through the exact
geometric graph refinement to its coarse measure. -/
theorem exact_subdivision_pushforward (region : CoarseRegion) :
    Measure.map (curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure data.graphMeasure.finePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor fine coverDensity)
        (senguptaTriangulatedTwistedRegionFactor fine coverDensity)) =
    senguptaCompactSurfaceGraphMeasure coarsePartitionFunction bundleClass region
      (senguptaTriangulatedRegionFactor coarse coverDensity)
      (senguptaTriangulatedTwistedRegionFactor coarse coverDensity) :=
  data.exact_graphMeasure_pushforward region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile density probe: an arbitrary function lacking the normalized convolution-semigroup
certificate cannot enter this specialized transport. -/
theorem missing_cover_semigroup_blocked
    (missing : ¬NormalizedCompactHaarDensitySemigroupData coverDensity) : False :=
  missing data.coverSemigroup

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
include data in
/-- Hostile twist probe: a noncentral fixed twist cannot enter this projection-free layer. Kernel
membership remains the responsibility of the outer covering-group finite-law wrapper. -/
theorem noncentral_twist_blocked
    (noncentral : ¬∀ element, bundleClass * element = element * bundleClass) : False :=
  noncentral data.bundleClass_central

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile dependency probe: an unrelated curve refinement cannot be substituted for the one in
the embedded subdivision geometry. -/
theorem changed_curve_refinement_blocked
    (changed : data.graphMeasure.curveRefinement ≠ curveRefinement) : False :=
  changed data.curveRefinement_eq

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile factor probe: changing any ordinary fine factor is rejected. -/
theorem changed_fine_ordinary_factor_blocked (region : CoarseRegion)
    (external : FineEdge → CoverGroup)
    (changed : data.graphMeasure.fineOrdinaryRegionWeight region external ≠
      senguptaTriangulatedRegionFactor fine coverDensity region external) : False :=
  changed (data.fineOrdinaryRegionWeight_eq region external)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile twist probe: changing the fixed central-twist slice of the fine twisted factor is
rejected without strengthening the source claim to arbitrary twists. -/
theorem changed_fine_twisted_factor_blocked
    (region : CoarseRegion) (external : FineEdge → CoverGroup)
    (changed : data.graphMeasure.fineTwistedRegionWeight bundleClass region external ≠
      senguptaTriangulatedTwistedRegionFactor fine coverDensity bundleClass region external) :
    False :=
  changed (data.fineTwistedRegionWeight_eq region external)

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Nonempty Curve] in
/-- Hostile analytic probe: changing the exact geometric weighted pushforward is rejected. -/
theorem changed_subdivision_pushforward_blocked (region : CoarseRegion)
    (changed : Measure.map (curveRefinement.graph.configurationMap (G := CoverGroup))
        (senguptaCompactSurfaceGraphMeasure data.graphMeasure.finePartitionFunction bundleClass region
          (senguptaTriangulatedRegionFactor fine coverDensity)
          (senguptaTriangulatedTwistedRegionFactor fine coverDensity)) ≠
      senguptaCompactSurfaceGraphMeasure coarsePartitionFunction bundleClass region
        (senguptaTriangulatedRegionFactor coarse coverDensity)
        (senguptaTriangulatedTwistedRegionFactor coarse coverDensity)) : False :=
  changed (data.exact_graphMeasure_pushforward region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaParameterizedSubdivisionGraphMeasureTransport.Probes
