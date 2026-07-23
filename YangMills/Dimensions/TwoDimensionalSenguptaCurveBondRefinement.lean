/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLaw
import YangMills.Mathematics.FiniteGraphRefinement

/-!
# Sengupta curve-bond refinement

This file supplies the exact combinatorial and measure-level interface missing from the curve-fixed
Fact 2 subclass. Every coarse graph bond is a fine oriented word, and every fine curve word is the
literal substitution of those words into the coarse curve. Consequently simultaneous covering and
projected curve holonomies commute with the refinement configuration map. A graph-measure
pushforward therefore transports the complete finite curve-holonomy law.

No fine heat-factor measure or source-valid subdivision is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uCoarseVertex uFineVertex uCoarseEdge uFineEdge uCurve uCover uG

variable
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} [Fintype CoarseEdge]
    {FineEdge : Type uFineEdge} [Fintype FineEdge]
    {Curve : Type uCurve}
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {CoverGroup : Type uCover} [Group CoverGroup]
    {G : Type uG} [Group G]
    {coarseCurveWord : Curve → List (OrientedEdge CoarseEdge)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}

/-- Exact graph and indexed-curve-word refinement, allowing curve bonds themselves to split. -/
structure TwoDimensionalSenguptaCurveBondRefinementData where
  curve_finite : Fintype Curve
  curve_nonempty : Nonempty Curve
  coarseCurveWord_nonempty : ∀ curve, coarseCurveWord curve ≠ []
  fineCurveWord_nonempty : ∀ curve, fineCurveWord curve ≠ []
  graph : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
    coarseSource coarseTarget fineSource fineTarget
  curveWord_refinement : ∀ curve,
    fineCurveWord curve = refineOrientedWord graph.edgeWord (coarseCurveWord curve)

namespace TwoDimensionalSenguptaCurveBondRefinementData

/-- Covering-group curve holonomies commute exactly with curve-bond refinement. -/
theorem coveringCurveHolonomy_commutes
    (data : TwoDimensionalSenguptaCurveBondRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (fineCurveWord := fineCurveWord))
    (configuration : FineEdge → CoverGroup) :
    (fun curve => finiteOrientedWordHolonomy
      (data.graph.configurationMap (G := CoverGroup) configuration) (coarseCurveWord curve)) =
    (fun curve => finiteOrientedWordHolonomy configuration (fineCurveWord curve)) := by
  funext curve
  rw [data.curveWord_refinement curve]
  exact (finiteOrientedWordHolonomy_refineOrientedWord
    data.graph.edgeWord configuration (coarseCurveWord curve)).symm

/-- Physical projected curve holonomies commute with the same exact refinement. -/
theorem projectedCurveHolonomy_commutes
    (data : TwoDimensionalSenguptaCurveBondRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (fineCurveWord := fineCurveWord))
    (projection : CoverGroup →* G) (configuration : FineEdge → CoverGroup) :
    senguptaFiniteGraphHolonomy projection coarseCurveWord
        (data.graph.configurationMap (G := CoverGroup) configuration) =
      senguptaFiniteGraphHolonomy projection fineCurveWord configuration := by
  funext curve
  exact congrArg projection
    (congrFun (data.coveringCurveHolonomy_commutes configuration) curve)

variable [MeasurableSpace CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [MeasurableSpace G]

omit [Fintype FineEdge] in
/-- The projected finite-curve holonomy map is measurable when the projection is measurable. -/
theorem projectedCurveHolonomy_measurable
    (projection : CoverGroup →* G) (projection_measurable : Measurable projection)
    (words : Curve → List (OrientedEdge FineEdge)) :
    Measurable (senguptaFiniteGraphHolonomy projection words) := by
  apply measurable_pi_iff.mpr
  intro curve
  exact projection_measurable.comp
    (finiteOrientedWordHolonomy_measurable (words curve))

/-- Any exact graph-configuration pushforward transports the complete projected curve-holonomy law.
This separates graph-measure construction from the purely formal curve-bond compatibility. -/
theorem map_projectedCurveHolonomy_eq
    (data : TwoDimensionalSenguptaCurveBondRefinementData
      (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (coarseCurveWord := coarseCurveWord) (fineCurveWord := fineCurveWord))
    (projection : CoverGroup →* G) (projection_measurable : Measurable projection)
    (fineMeasure : Measure (FineEdge → CoverGroup))
    (coarseMeasure : Measure (CoarseEdge → CoverGroup))
    (measure_refinement : Measure.map (data.graph.configurationMap (G := CoverGroup)) fineMeasure = coarseMeasure) :
    Measure.map (senguptaFiniteGraphHolonomy projection coarseCurveWord) coarseMeasure =
      Measure.map (senguptaFiniteGraphHolonomy projection fineCurveWord) fineMeasure := by
  rw [← measure_refinement]
  rw [Measure.map_map
    (projectedCurveHolonomy_measurable projection projection_measurable coarseCurveWord)
    (data.graph.configurationMap_measurable (G := CoverGroup))]
  congr 1
  funext configuration
  exact data.projectedCurveHolonomy_commutes projection configuration

end TwoDimensionalSenguptaCurveBondRefinementData

end

end YangMills.Dimensions
