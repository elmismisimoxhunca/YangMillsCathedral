/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinement

/-!
# Composition of Sengupta curve-bond refinements

Two exact curve-bond refinements compose through literal oriented-word substitution. The direct
graph map is the composite fine-to-middle-to-coarse configuration map, exact measure pushforwards
compose, and the complete projected finite-curve law transports along the direct refinement.

This reusable layer constructs no graph measure, heat factor, or embedded subdivision.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uCoarseVertex uMiddleVertex uFineVertex uCoarseEdge uMiddleEdge uFineEdge
  uCurve uCover uG

variable
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uMiddleVertex}
    {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} [Fintype CoarseEdge]
    {MiddleEdge : Type uMiddleEdge} [Fintype MiddleEdge]
    {FineEdge : Type uFineEdge} [Fintype FineEdge]
    {Curve : Type uCurve}
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseCurveWord : Curve → List (OrientedEdge CoarseEdge)}
    {middleCurveWord : Curve → List (OrientedEdge MiddleEdge)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}

/-- Exact coherent triple of coarse-to-middle, middle-to-fine, and direct graph refinements, with
curve words fixed at all three stages. -/
structure TwoDimensionalSenguptaCurveBondRefinementCompositionData where
  coarseToMiddle : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := coarseSource) (coarseTarget := coarseTarget)
    (fineSource := middleSource) (fineTarget := middleTarget)
    (coarseCurveWord := coarseCurveWord) (fineCurveWord := middleCurveWord)
  middleToFine : TwoDimensionalSenguptaCurveBondRefinementData
    (coarseSource := middleSource) (coarseTarget := middleTarget)
    (fineSource := fineSource) (fineTarget := fineTarget)
    (coarseCurveWord := middleCurveWord) (fineCurveWord := fineCurveWord)
  directGraph : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
    coarseSource coarseTarget fineSource fineTarget
  graphComposition : FiniteGraphRefinementCompositionData
    coarseToMiddle.graph middleToFine.graph directGraph

namespace TwoDimensionalSenguptaCurveBondRefinementCompositionData

/-- The direct curve refinement is derived from the two exact stages and graph-word composition. -/
noncomputable def direct
    (data : TwoDimensionalSenguptaCurveBondRefinementCompositionData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (middleCurveWord := middleCurveWord)
      (fineCurveWord := fineCurveWord)) :
    TwoDimensionalSenguptaCurveBondRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (fineCurveWord := fineCurveWord) where
  curve_finite := data.coarseToMiddle.curve_finite
  curve_nonempty := data.coarseToMiddle.curve_nonempty
  coarseCurveWord_nonempty := data.coarseToMiddle.coarseCurveWord_nonempty
  fineCurveWord_nonempty := data.middleToFine.fineCurveWord_nonempty
  graph := data.directGraph
  curveWord_refinement curve := by
    calc
      fineCurveWord curve = refineOrientedWord data.middleToFine.graph.edgeWord
          (middleCurveWord curve) := data.middleToFine.curveWord_refinement curve
      _ = refineOrientedWord data.middleToFine.graph.edgeWord
          (refineOrientedWord data.coarseToMiddle.graph.edgeWord
            (coarseCurveWord curve)) := by
        rw [data.coarseToMiddle.curveWord_refinement curve]
      _ = refineOrientedWord
          (fun edge => refineOrientedWord data.middleToFine.graph.edgeWord
            (data.coarseToMiddle.graph.edgeWord edge)) (coarseCurveWord curve) :=
        refineOrientedWord_comp data.coarseToMiddle.graph.edgeWord
          data.middleToFine.graph.edgeWord (coarseCurveWord curve)
      _ = refineOrientedWord data.directGraph.edgeWord (coarseCurveWord curve) := by
        congr 1
        funext edge
        exact (data.graphComposition.edgeWord_eq edge).symm

/-- Any other direct graph coherent with the same two curve-refinement stages equals the stored
direct graph. The direct graph remains an existence input, but its data are unique. -/
theorem directGraph_unique
    (data : TwoDimensionalSenguptaCurveBondRefinementCompositionData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (middleCurveWord := middleCurveWord)
      (fineCurveWord := fineCurveWord))
    {otherDirect : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget}
    (otherComposition : FiniteGraphRefinementCompositionData
      data.coarseToMiddle.graph data.middleToFine.graph otherDirect) :
    data.directGraph = otherDirect :=
  data.graphComposition.directGraph_unique otherComposition

/-- The direct fine-to-coarse configuration map is literally the composite of both stage maps. -/
theorem direct_configurationMap_eq_comp
    (data : TwoDimensionalSenguptaCurveBondRefinementCompositionData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (middleCurveWord := middleCurveWord)
      (fineCurveWord := fineCurveWord))
    {CoverGroup : Type uCover} [Group CoverGroup] :
    data.directGraph.configurationMap (G := CoverGroup) =
      data.coarseToMiddle.graph.configurationMap ∘
        data.middleToFine.graph.configurationMap :=
  data.graphComposition.configurationMap_eq_comp

variable {CoverGroup : Type uCover} [Group CoverGroup]
    [MeasurableSpace CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]

/-- Fine-to-middle and middle-to-coarse measure laws compose to the exact direct graph law. -/
theorem direct_measure_pushforward
    (data : TwoDimensionalSenguptaCurveBondRefinementCompositionData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (middleCurveWord := middleCurveWord)
      (fineCurveWord := fineCurveWord))
    (fineMeasure : Measure (FineEdge → CoverGroup))
    (middleMeasure : Measure (MiddleEdge → CoverGroup))
    (coarseMeasure : Measure (CoarseEdge → CoverGroup))
    (fine_pushforward :
      Measure.map (data.middleToFine.graph.configurationMap (G := CoverGroup)) fineMeasure =
        middleMeasure)
    (middle_pushforward :
      Measure.map (data.coarseToMiddle.graph.configurationMap (G := CoverGroup)) middleMeasure =
        coarseMeasure) :
    Measure.map (data.directGraph.configurationMap (G := CoverGroup)) fineMeasure =
      coarseMeasure := by
  rw [data.direct_configurationMap_eq_comp (CoverGroup := CoverGroup)]
  exact finiteRefinementMeasurePushforward_comp fineMeasure middleMeasure coarseMeasure
    data.middleToFine.graph.configurationMap data.coarseToMiddle.graph.configurationMap
    data.middleToFine.graph.configurationMap_measurable
    data.coarseToMiddle.graph.configurationMap_measurable
    fine_pushforward middle_pushforward

variable {G : Type uG} [Group G] [MeasurableSpace G]

/-- Consequently the complete projected finite-curve law transports directly across both stages. -/
theorem map_projectedCurveHolonomy_eq
    (data : TwoDimensionalSenguptaCurveBondRefinementCompositionData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (middleCurveWord := middleCurveWord)
      (fineCurveWord := fineCurveWord))
    (projection : CoverGroup →* G) (projection_measurable : Measurable projection)
    (fineMeasure : Measure (FineEdge → CoverGroup))
    (middleMeasure : Measure (MiddleEdge → CoverGroup))
    (coarseMeasure : Measure (CoarseEdge → CoverGroup))
    (fine_pushforward :
      Measure.map (data.middleToFine.graph.configurationMap (G := CoverGroup)) fineMeasure =
        middleMeasure)
    (middle_pushforward :
      Measure.map (data.coarseToMiddle.graph.configurationMap (G := CoverGroup)) middleMeasure =
        coarseMeasure) :
    Measure.map (senguptaFiniteGraphHolonomy projection coarseCurveWord) coarseMeasure =
      Measure.map (senguptaFiniteGraphHolonomy projection fineCurveWord) fineMeasure :=
  data.direct.map_projectedCurveHolonomy_eq projection projection_measurable
    fineMeasure coarseMeasure
    (data.direct_measure_pushforward fineMeasure middleMeasure coarseMeasure
      fine_pushforward middle_pushforward)

end TwoDimensionalSenguptaCurveBondRefinementCompositionData

end

end YangMills.Dimensions
