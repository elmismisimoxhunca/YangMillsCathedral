/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinementComposition

/-! Hostile probes for composed Sengupta curve-bond refinements. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinementComposition.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

variable
    {CoarseVertex MiddleVertex FineVertex CoarseEdge MiddleEdge FineEdge Curve : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseCurveWord : Curve → List (OrientedEdge CoarseEdge)}
    {middleCurveWord : Curve → List (OrientedEdge MiddleEdge)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    (data : TwoDimensionalSenguptaCurveBondRefinementCompositionData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (middleCurveWord := middleCurveWord)
      (fineCurveWord := fineCurveWord))

/-- Two exact curve refinements produce the literal direct curve-word substitution. -/
theorem exact_direct_curve_word (curve : Curve) :
    fineCurveWord curve =
      refineOrientedWord data.directGraph.edgeWord (coarseCurveWord curve) :=
  data.direct.curveWord_refinement curve

/-- Hostile direct-word probe: the certified direct edge words cannot differ from composition. -/
theorem changed_direct_edge_word_blocked (edge : CoarseEdge)
    (changed : data.directGraph.edgeWord edge ≠
      refineOrientedWord data.middleToFine.graph.edgeWord
        (data.coarseToMiddle.graph.edgeWord edge)) : False :=
  changed (data.graphComposition.edgeWord_eq edge)

/-- The direct configuration map is exactly the two-stage map. -/
theorem exact_configuration_composition {H : Type*} [Group H] :
    data.directGraph.configurationMap (G := H) =
      data.coarseToMiddle.graph.configurationMap ∘
        data.middleToFine.graph.configurationMap :=
  data.direct_configurationMap_eq_comp

variable {CoverGroup : Type*} [Group CoverGroup]
    [MeasurableSpace CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]

/-- Exact stagewise graph-measure laws force the direct pushforward. -/
theorem exact_measure_composition
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
      coarseMeasure :=
  data.direct_measure_pushforward fineMeasure middleMeasure coarseMeasure
    fine_pushforward middle_pushforward

/-- Hostile measure probe: changing the direct pushforward is rejected. -/
theorem changed_direct_measure_blocked
    (fineMeasure : Measure (FineEdge → CoverGroup))
    (middleMeasure : Measure (MiddleEdge → CoverGroup))
    (coarseMeasure : Measure (CoarseEdge → CoverGroup))
    (fine_pushforward :
      Measure.map (data.middleToFine.graph.configurationMap (G := CoverGroup)) fineMeasure =
        middleMeasure)
    (middle_pushforward :
      Measure.map (data.coarseToMiddle.graph.configurationMap (G := CoverGroup)) middleMeasure =
        coarseMeasure)
    (changed : Measure.map (data.directGraph.configurationMap (G := CoverGroup)) fineMeasure ≠
      coarseMeasure) : False :=
  changed (data.direct_measure_pushforward fineMeasure middleMeasure coarseMeasure
    fine_pushforward middle_pushforward)

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- The complete projected finite-curve law transports across the exact two-stage chain. -/
theorem exact_projected_law_composition
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
  data.map_projectedCurveHolonomy_eq projection projection_measurable
    fineMeasure middleMeasure coarseMeasure fine_pushforward middle_pushforward

end

end YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinementComposition.Probes
