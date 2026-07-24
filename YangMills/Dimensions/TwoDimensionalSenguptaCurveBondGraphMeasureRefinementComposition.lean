/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinement
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinementComposition

/-!
# Composition of Sengupta weighted graph-measure refinements

A coarse-to-middle equation-(8.3) graph-measure refinement and a supplied fine-to-middle weighted
pushforward compose along one coherent curve-bond refinement triple. The direct fine-to-coarse
weighted graph-measure refinement and complete projected finite-curve law are derived.

The coherent direct graph is canonically constructible from the two refinement stages; this record
stores that composition data together with both supplied weighted measures and stagewise pushforwards.
No heat-factor integration or embedded preliminary subdivision is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uG uCover uCurve uCoarseEdge uMiddleEdge uFineEdge uRegion uSample
  uCoarseVertex uMiddleVertex uFineVertex

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    {Curve : Type uCurve} [Fintype Curve] [Nonempty Curve]
    {CoarseEdge : Type uCoarseEdge} [Fintype CoarseEdge] [DecidableEq CoarseEdge]
    {MiddleEdge : Type uMiddleEdge} [Fintype MiddleEdge]
    {FineEdge : Type uFineEdge} [Fintype FineEdge]
    {Region : Type uRegion} [Fintype Region] [DecidableEq Region]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uMiddleVertex}
    {FineVertex : Type uFineVertex}
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := CoarseEdge)
      (Region := Region) (Sample := Sample)}
    {middleCurveWord : Curve → List (OrientedEdge MiddleEdge)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}

/-- Exact two-stage equation-(8.3) weighted graph-measure refinement data. -/
structure TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData where
  curveComposition : TwoDimensionalSenguptaCurveBondRefinementCompositionData
    (coarseSource := coarseSource) (coarseTarget := coarseTarget)
    (middleSource := middleSource) (middleTarget := middleTarget)
    (fineSource := fineSource) (fineTarget := fineTarget)
    (coarseCurveWord := coarseLaw.curveWord) (middleCurveWord := middleCurveWord)
    (fineCurveWord := fineCurveWord)
  coarseToMiddleMeasure : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
    (coarseLaw := coarseLaw)
    (coarseSource := coarseSource) (coarseTarget := coarseTarget)
    (fineSource := middleSource) (fineTarget := middleTarget)
    (fineCurveWord := middleCurveWord)
  coarseToMiddle_curveRefinement_eq :
    coarseToMiddleMeasure.curveRefinement = curveComposition.coarseToMiddle
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
  fineToMiddle_pushforward : ∀ region,
    Measure.map (curveComposition.middleToFine.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure finePartitionFunction coarseLaw.bundleClass region
        fineOrdinaryRegionWeight fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarseToMiddleMeasure.finePartitionFunction
      coarseLaw.bundleClass region coarseToMiddleMeasure.fineOrdinaryRegionWeight
      coarseToMiddleMeasure.fineTwistedRegionWeight

namespace TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData

/-- The exact direct fine-to-coarse equation-(8.3) refinement, derived from both stage laws. -/
noncomputable def direct
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (middleCurveWord := middleCurveWord) (fineCurveWord := fineCurveWord)) :
    TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord) where
  curveRefinement := data.curveComposition.direct
  projection_measurable := data.coarseToMiddleMeasure.projection_measurable
  fineOrdinaryRegionWeight := data.fineOrdinaryRegionWeight
  fineTwistedRegionWeight := data.fineTwistedRegionWeight
  finePartitionFunction := data.finePartitionFunction
  fineGraphWeight_measurable := data.fineGraphWeight_measurable
  finePartitionFunction_eq_lintegral := data.finePartitionFunction_eq_lintegral
  finePartitionFunction_ne_zero := data.finePartitionFunction_ne_zero
  finePartitionFunction_ne_top := data.finePartitionFunction_ne_top
  graphMeasure_pushforward region := by
    apply data.curveComposition.direct_measure_pushforward
      (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
        data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight)
      (senguptaCompactSurfaceGraphMeasure data.coarseToMiddleMeasure.finePartitionFunction
        coarseLaw.bundleClass region data.coarseToMiddleMeasure.fineOrdinaryRegionWeight
        data.coarseToMiddleMeasure.fineTwistedRegionWeight)
      (senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
        coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight)
      (data.fineToMiddle_pushforward region)
    rw [← data.coarseToMiddle_curveRefinement_eq]
    exact data.coarseToMiddleMeasure.graphMeasure_pushforward region

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- The complete stochastic projected finite-curve law is represented directly on the finest graph. -/
theorem finiteDimensionalLaw_on_fineGraph
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (middleCurveWord := middleCurveWord) (fineCurveWord := fineCurveWord))
    (region : Region) :
    Measure.map coarseLaw.sampleHolonomy coarseLaw.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy coarseLaw.projection fineCurveWord)
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) :=
  data.direct.finiteDimensionalLaw_on_fineGraph region

end TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData

end

end YangMills.Dimensions
