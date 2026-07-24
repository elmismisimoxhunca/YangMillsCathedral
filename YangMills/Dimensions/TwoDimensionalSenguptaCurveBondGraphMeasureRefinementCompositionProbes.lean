/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinementComposition

/-! Hostile probes for composed weighted curve-bond graph refinements. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinementComposition.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

variable
    {G CoverGroup Curve CoarseEdge MiddleEdge FineEdge Region Sample
      CoarseVertex MiddleVertex FineVertex : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [Group CoverGroup] [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup] [MeasurableSpace CoverGroup]
    [BorelSpace CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve]
    [Fintype CoarseEdge] [DecidableEq CoarseEdge]
    [Fintype MiddleEdge] [Fintype FineEdge]
    [Fintype Region] [DecidableEq Region] [MeasurableSpace Sample]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := CoarseEdge)
      (Region := Region) (Sample := Sample)}
    {middleCurveWord : Curve → List (OrientedEdge MiddleEdge)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementCompositionData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (middleSource := middleSource) (middleTarget := middleTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (middleCurveWord := middleCurveWord) (fineCurveWord := fineCurveWord))

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- The direct weighted refinement uses the exact derived direct curve refinement. -/
theorem exact_direct_curve_dependency :
    data.direct.curveRefinement = data.curveComposition.direct :=
  rfl

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- The direct graph-measure pushforward is derived from both exact stages. -/
theorem exact_direct_weighted_pushforward (region : Region) :
    Measure.map (data.curveComposition.directGraph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
        data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
      coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight :=
  data.direct.graphMeasure_pushforward region

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] in
/-- The complete stochastic finite law is represented on the finest graph. -/
theorem exact_fine_finite_law (region : Region) :
    Measure.map coarseLaw.sampleHolonomy coarseLaw.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy coarseLaw.projection fineCurveWord)
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) :=
  data.finiteDimensionalLaw_on_fineGraph region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] in
/-- Hostile middle-law probe: the first stage cannot use a different curve refinement. -/
theorem changed_middle_curve_refinement_blocked
    (changed : data.coarseToMiddleMeasure.curveRefinement ≠
      data.curveComposition.coarseToMiddle) : False :=
  changed data.coarseToMiddle_curveRefinement_eq

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] in
/-- The direct configuration map remains surjective after composing both exact refinement stages. -/
theorem direct_configurationMap_surjective : Function.Surjective
    ((data.direct).curveRefinement.graph.configurationMap (G := CoverGroup)) :=
  (data.direct).configurationMap_surjective

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] in
/-- Hostile stage probe: a nonsurjective fine-to-middle map cannot enter the composition. -/
theorem nonsurjective_fine_to_middle_blocked
    (changed : ¬Function.Surjective
      (data.curveComposition.middleToFine.graph.configurationMap (G := CoverGroup))) : False :=
  changed data.fineToMiddle_configurationMap_surjective

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] in
/-- Hostile stage-law probe: changing the supplied fine-to-middle pushforward is rejected. -/
theorem changed_fine_to_middle_pushforward_blocked (region : Region)
    (changed : Measure.map
        (data.curveComposition.middleToFine.graph.configurationMap (G := CoverGroup))
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) ≠
      senguptaCompactSurfaceGraphMeasure data.coarseToMiddleMeasure.finePartitionFunction
        coarseLaw.bundleClass region data.coarseToMiddleMeasure.fineOrdinaryRegionWeight
        data.coarseToMiddleMeasure.fineTwistedRegionWeight) : False :=
  changed (data.fineToMiddle_pushforward region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinementComposition.Probes
