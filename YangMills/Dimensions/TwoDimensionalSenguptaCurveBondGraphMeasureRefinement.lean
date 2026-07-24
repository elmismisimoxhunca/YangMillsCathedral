/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinement

/-!
# Sengupta graph-measure refinement across split curve bonds

This file joins exact curve-bond substitution to the actual normalized weighted graph measure in
Sengupta's equation (8.3). A supplied fine weighted graph measure must push forward to the coarse
weighted graph measure through the exact finite-graph configuration map, for every choice of
complementary distinguished region. The complete projected finite-curve law then transports to the
fine graph, and normalization/nonzeroness of the fine graph measure are derived.

This remains a conditional acceptance interface. It does not construct the fine heat factors, prove
the weighted-measure pushforward, or construct a source-valid embedded subdivision.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uG uCover uCurve uCoarseEdge uFineEdge uRegion uSample uCoarseVertex uFineVertex

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {CoarseEdge : Type uCoarseEdge} [Fintype CoarseEdge] [DecidableEq CoarseEdge]
    {FineEdge : Type uFineEdge} [Fintype FineEdge]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := CoarseEdge)
      (Region := Region) (Sample := Sample)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}

/-- A fine equation-(8.3) graph measure whose exact configuration pushforward is the coarse one,
including refinements that split bonds traversed by the selected curves. -/
structure TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData where
  curveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := coarseSource) (coarseTarget := coarseTarget)
    (fineSource := fineSource) (fineTarget := fineTarget)
    (coarseCurveWord := coarseLaw.curveWord) (fineCurveWord := fineCurveWord)
  projection_measurable : Measurable coarseLaw.projection
  fineOrdinaryRegionWeight : Region → (FineEdge → CoverGroup) → ℝ≥0∞
  fineTwistedRegionWeight : CoverGroup → Region → (FineEdge → CoverGroup) → ℝ≥0∞
  finePartitionFunction : ℝ≥0∞
  fineGraphWeight_measurable : Measurable
    (senguptaCompactSurfaceGraphWeight coarseLaw.bundleClass coarseLaw.distinguishedRegion
      fineOrdinaryRegionWeight fineTwistedRegionWeight)
  finePartitionFunction_eq_lintegral : finePartitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight coarseLaw.bundleClass
      coarseLaw.distinguishedRegion fineOrdinaryRegionWeight fineTwistedRegionWeight field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := FineEdge) (G := CoverGroup)
  finePartitionFunction_ne_zero : finePartitionFunction ≠ 0
  finePartitionFunction_ne_top : finePartitionFunction ≠ ⊤
  /-- The actual weighted graph-measure compatibility required for the split-bond refinement. -/
  graphMeasure_pushforward : ∀ region,
    Measure.map (curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure finePartitionFunction coarseLaw.bundleClass region
        fineOrdinaryRegionWeight fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
      coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight

namespace TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The supplied pushforward is literally between the fine and coarse equation-(8.3) graph
measures, not between unrelated auxiliary measures. -/
theorem exact_graphMeasure_pushforward
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord))
    (region : Region) :
    Measure.map (data.curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
        data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
      coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight :=
  data.graphMeasure_pushforward region

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- Every fine distinguished-region graph measure is normalized, derived from the coarse stochastic
law and the exact graph-measure pushforward. -/
theorem fineGraphMeasure_univ
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord))
    (region : Region) :
    senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
      data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight Set.univ = 1 := by
  have pushed := congrArg (fun measure : Measure (CoarseEdge → CoverGroup) => measure Set.univ)
    (data.graphMeasure_pushforward region)
  rw [Measure.map_apply data.curveRefinement.graph.configurationMap_measurable
    MeasurableSet.univ] at pushed
  simpa [coarseLaw.graphMeasure_univ region] using pushed

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- Therefore no fine weighted graph measure can be the zero measure. -/
theorem fineGraphMeasure_ne_zero
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord))
    (region : Region) :
    senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
      data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight ≠ 0 := by
  intro zeroMeasure
  have normalized := data.fineGraphMeasure_univ region
  rw [zeroMeasure] at normalized
  simp at normalized

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- Sengupta's complete finite projected holonomy law may be evaluated on the split-bond fine graph
at every distinguished region. -/
theorem finiteDimensionalLaw_on_fineGraph
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord))
    (region : Region) :
    Measure.map coarseLaw.sampleHolonomy coarseLaw.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy coarseLaw.projection fineCurveWord)
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) := by
  rw [coarseLaw.finiteDimensionalLaw_atRegion region]
  exact data.curveRefinement.map_projectedCurveHolonomy_eq
    coarseLaw.projection data.projection_measurable
    (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
      data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight)
    (senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
      coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight)
    (data.graphMeasure_pushforward region)

end TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData

end

end YangMills.Dimensions
