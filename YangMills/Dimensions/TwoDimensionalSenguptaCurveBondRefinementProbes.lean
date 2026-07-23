/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinement

/-! Hostile probes for Sengupta curve-bond refinement. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinement.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

variable
    {CoarseVertex FineVertex CoarseEdge FineEdge Curve CoverGroup G : Type*}
    [Fintype CoarseEdge] [Fintype FineEdge]
    [Group CoverGroup] [Group G]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseCurveWord : Curve → List (OrientedEdge CoarseEdge)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    (data : TwoDimensionalSenguptaCurveBondRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (fineCurveWord := fineCurveWord))

include data in
/-- The curve carrier is finite/nonempty and neither coarse nor fine indexed paths are empty. -/
theorem exact_curve_nonvacuity (curve : Curve) :
    Nonempty Curve ∧ Nonempty (Fintype Curve) ∧
      coarseCurveWord curve ≠ [] ∧ fineCurveWord curve ≠ [] :=
  ⟨data.curve_nonempty, ⟨data.curve_finite⟩,
    data.coarseCurveWord_nonempty curve, data.fineCurveWord_nonempty curve⟩

include data in
/-- An empty curve carrier cannot satisfy the refinement interface. -/
theorem empty_curve_carrier_blocked (empty : IsEmpty Curve) : False :=
  empty.false data.curve_nonempty.some

include data in
/-- An empty indexed curve word is rejected before holonomy transport. -/
theorem empty_coarse_curve_word_blocked (curve : Curve)
    (empty : coarseCurveWord curve = []) : False :=
  data.coarseCurveWord_nonempty curve empty

/-- Fine curve words are literal coarse-word substitution, including split curve bonds. -/
theorem exact_curve_word_substitution (curve : Curve) :
    fineCurveWord curve = refineOrientedWord data.graph.edgeWord (coarseCurveWord curve) :=
  data.curveWord_refinement curve

/-- Covering and projected holonomies commute with the exact graph configuration map. -/
theorem exact_curve_holonomy_transport (projection : CoverGroup →* G)
    (configuration : FineEdge → CoverGroup) :
    (fun curve => finiteOrientedWordHolonomy
      (data.graph.configurationMap (G := CoverGroup) configuration) (coarseCurveWord curve)) =
      (fun curve => finiteOrientedWordHolonomy configuration (fineCurveWord curve)) ∧
    senguptaFiniteGraphHolonomy projection coarseCurveWord
        (data.graph.configurationMap (G := CoverGroup) configuration) =
      senguptaFiniteGraphHolonomy projection fineCurveWord configuration :=
  ⟨data.coveringCurveHolonomy_commutes configuration,
    data.projectedCurveHolonomy_commutes projection configuration⟩

/-- Hostile word probe: changing one refined indexed curve is rejected. -/
theorem changed_curve_word_blocked (curve : Curve)
    (changed : fineCurveWord curve ≠
      refineOrientedWord data.graph.edgeWord (coarseCurveWord curve)) : False :=
  changed (data.curveWord_refinement curve)

/-- Hostile holonomy probe: the same exact projected curve family cannot change. -/
theorem changed_projected_holonomy_blocked (projection : CoverGroup →* G)
    (configuration : FineEdge → CoverGroup)
    (changed : senguptaFiniteGraphHolonomy projection coarseCurveWord
        (data.graph.configurationMap (G := CoverGroup) configuration) ≠
      senguptaFiniteGraphHolonomy projection fineCurveWord configuration) : False :=
  changed (data.projectedCurveHolonomy_commutes projection configuration)

variable [MeasurableSpace CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [MeasurableSpace G]

/-- A graph-measure refinement law transports the complete finite projected curve law. -/
theorem exact_measure_transport (projection : CoverGroup →* G)
    (projection_measurable : Measurable projection)
    (fineMeasure : Measure (FineEdge → CoverGroup))
    (coarseMeasure : Measure (CoarseEdge → CoverGroup))
    (measure_refinement :
      Measure.map (data.graph.configurationMap (G := CoverGroup)) fineMeasure = coarseMeasure) :
    Measure.map (senguptaFiniteGraphHolonomy projection coarseCurveWord) coarseMeasure =
      Measure.map (senguptaFiniteGraphHolonomy projection fineCurveWord) fineMeasure :=
  data.map_projectedCurveHolonomy_eq projection projection_measurable fineMeasure coarseMeasure
    measure_refinement

end

end YangMills.Dimensions.TwoDimensionalSenguptaCurveBondRefinement.Probes
