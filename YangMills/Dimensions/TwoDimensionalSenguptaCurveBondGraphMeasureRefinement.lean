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

/-- Parameterized equation-(8.3) graph-measure refinement independent of a physical projection,
sample law, or pre-existing finite-law wrapper. Both coarse and fine weights and normalizers are
explicit, and the exact refinement map pushes the fine weighted measure to the coarse one. -/
structure TwoDimensionalSenguptaParameterizedCurveBondGraphMeasureRefinementData
    (coarseCurveWord : Curve → List (OrientedEdge CoarseEdge))
    (bundleClass : CoverGroup)
    (coarseOrdinaryRegionWeight : Region → (CoarseEdge → CoverGroup) → ℝ≥0∞)
    (coarseTwistedRegionWeight : CoverGroup → Region → (CoarseEdge → CoverGroup) → ℝ≥0∞)
    (coarsePartitionFunction : ℝ≥0∞)
    (distinguishedRegion : Region)
    (parameterizedFineCurveWord : Curve → List (OrientedEdge FineEdge)) where
  curveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := coarseSource) (coarseTarget := coarseTarget)
    (fineSource := fineSource) (fineTarget := fineTarget)
    (coarseCurveWord := coarseCurveWord) (fineCurveWord := parameterizedFineCurveWord)
  configurationMap_surjective : Function.Surjective
    (curveRefinement.graph.configurationMap (G := CoverGroup))
  coarseGraphWeight_measurable : Measurable
    (senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      coarseOrdinaryRegionWeight coarseTwistedRegionWeight)
  coarsePartitionFunction_eq_lintegral : coarsePartitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      coarseOrdinaryRegionWeight coarseTwistedRegionWeight field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := CoarseEdge) (G := CoverGroup)
  coarsePartitionFunction_ne_zero : coarsePartitionFunction ≠ 0
  coarsePartitionFunction_ne_top : coarsePartitionFunction ≠ ⊤
  fineOrdinaryRegionWeight : Region → (FineEdge → CoverGroup) → ℝ≥0∞
  fineTwistedRegionWeight : CoverGroup → Region → (FineEdge → CoverGroup) → ℝ≥0∞
  finePartitionFunction : ℝ≥0∞
  fineGraphWeight_measurable : Measurable
    (senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      fineOrdinaryRegionWeight fineTwistedRegionWeight)
  finePartitionFunction_eq_lintegral : finePartitionFunction =
    ∫⁻ field, senguptaCompactSurfaceGraphWeight bundleClass distinguishedRegion
      fineOrdinaryRegionWeight fineTwistedRegionWeight field
      ∂normalizedCompactHaarFiniteProductMeasure (Edge := FineEdge) (G := CoverGroup)
  finePartitionFunction_ne_zero : finePartitionFunction ≠ 0
  finePartitionFunction_ne_top : finePartitionFunction ≠ ⊤
  coarseGraphMeasure_univ : ∀ region,
    senguptaCompactSurfaceGraphMeasure coarsePartitionFunction bundleClass region
      coarseOrdinaryRegionWeight coarseTwistedRegionWeight Set.univ = 1
  fineGraphMeasure_univ : ∀ region,
    senguptaCompactSurfaceGraphMeasure finePartitionFunction bundleClass region
      fineOrdinaryRegionWeight fineTwistedRegionWeight Set.univ = 1
  graphMeasure_pushforward : ∀ region,
    Measure.map (curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure finePartitionFunction bundleClass region
        fineOrdinaryRegionWeight fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarsePartitionFunction bundleClass region
      coarseOrdinaryRegionWeight coarseTwistedRegionWeight

/-- A fine equation-(8.3) graph measure whose exact configuration pushforward is the coarse one,
including refinements that split bonds traversed by the selected curves. -/
structure TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData where
  curveRefinement : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := coarseSource) (coarseTarget := coarseTarget)
    (fineSource := fineSource) (fineTarget := fineTarget)
    (coarseCurveWord := coarseLaw.curveWord) (fineCurveWord := fineCurveWord)
  configurationMap_surjective : Function.Surjective
    (curveRefinement.graph.configurationMap (G := CoverGroup))
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

namespace TwoDimensionalSenguptaParameterizedCurveBondGraphMeasureRefinementData

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup] in
/-- The parameterized certificate stores the literal weighted-measure pushforward for every
complementary distinguished region. -/
theorem exact_graphMeasure_pushforward
    {coarseCurveWord : Curve → List (OrientedEdge CoarseEdge)}
    {bundleClass : CoverGroup}
    {coarseOrdinaryRegionWeight : Region → (CoarseEdge → CoverGroup) → ℝ≥0∞}
    {coarseTwistedRegionWeight : CoverGroup → Region → (CoarseEdge → CoverGroup) → ℝ≥0∞}
    {coarsePartitionFunction : ℝ≥0∞} {distinguishedRegion : Region}
    (data : TwoDimensionalSenguptaParameterizedCurveBondGraphMeasureRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      coarseCurveWord bundleClass coarseOrdinaryRegionWeight coarseTwistedRegionWeight
      coarsePartitionFunction distinguishedRegion fineCurveWord)
    (region : Region) :
    Measure.map (data.curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction bundleClass region
        data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarsePartitionFunction bundleClass region
      coarseOrdinaryRegionWeight coarseTwistedRegionWeight :=
  data.graphMeasure_pushforward region

end TwoDimensionalSenguptaParameterizedCurveBondGraphMeasureRefinementData

namespace TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData

/-- Forget the physical projection and sample law while retaining the exact coarse/fine weighted
measures, normalizers, refinement, and pushforward. -/
noncomputable def toParameterized
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord)) :
    TwoDimensionalSenguptaParameterizedCurveBondGraphMeasureRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      coarseLaw.curveWord coarseLaw.bundleClass coarseLaw.ordinaryRegionWeight
      coarseLaw.twistedRegionWeight coarseLaw.partitionFunction coarseLaw.distinguishedRegion
      fineCurveWord where
  curveRefinement := data.curveRefinement
  configurationMap_surjective := data.configurationMap_surjective
  coarseGraphWeight_measurable := coarseLaw.graphWeight_measurable
  coarsePartitionFunction_eq_lintegral := coarseLaw.partitionFunction_eq_lintegral
  coarsePartitionFunction_ne_zero := coarseLaw.partitionFunction_ne_zero
  coarsePartitionFunction_ne_top := coarseLaw.partitionFunction_ne_top
  fineOrdinaryRegionWeight := data.fineOrdinaryRegionWeight
  fineTwistedRegionWeight := data.fineTwistedRegionWeight
  finePartitionFunction := data.finePartitionFunction
  fineGraphWeight_measurable := data.fineGraphWeight_measurable
  finePartitionFunction_eq_lintegral := data.finePartitionFunction_eq_lintegral
  finePartitionFunction_ne_zero := data.finePartitionFunction_ne_zero
  finePartitionFunction_ne_top := data.finePartitionFunction_ne_top
  coarseGraphMeasure_univ := coarseLaw.graphMeasure_univ
  fineGraphMeasure_univ region := by
    have pushforward := congrArg (fun measure : Measure (CoarseEdge → CoverGroup) =>
      measure Set.univ) (data.graphMeasure_pushforward region)
    rw [Measure.map_apply data.curveRefinement.graph.configurationMap_measurable MeasurableSet.univ]
      at pushforward
    simpa [coarseLaw.graphMeasure_univ region] using pushforward
  graphMeasure_pushforward := data.graphMeasure_pushforward

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
