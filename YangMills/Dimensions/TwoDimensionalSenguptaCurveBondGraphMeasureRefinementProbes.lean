/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinement

/-! Hostile probes for split-curve-bond weighted graph-measure refinement. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinement.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal

noncomputable section

variable
    {G CoverGroup Curve CoarseEdge FineEdge Region Sample CoarseVertex FineVertex : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [Group CoverGroup] [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [T2Space CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve]
    [Fintype CoarseEdge] [DecidableEq CoarseEdge]
    [Fintype FineEdge] [DecidableEq FineEdge]
    [Fintype Region] [DecidableEq Region]
    [MeasurableSpace Sample]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseLaw : TwoDimensionalSenguptaCompactSurfaceFiniteHolonomyLawData
      (G := G) (CoverGroup := CoverGroup) (Curve := Curve) (Edge := CoarseEdge)
      (Region := Region) (Sample := Sample)}
    {fineCurveWord : Curve → List (OrientedEdge FineEdge)}
    (data : TwoDimensionalSenguptaCurveBondGraphMeasureRefinementData
      (coarseLaw := coarseLaw) (coarseSource := coarseSource) (coarseTarget := coarseTarget)
      (fineSource := fineSource) (fineTarget := fineTarget)
      (fineCurveWord := fineCurveWord))

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
include data in
/-- The fine normalizer is tied to the literal fine graph-weight integral and is finite/nonzero. -/
theorem exact_fine_normalizer :
    data.finePartitionFunction =
      ∫⁻ field, senguptaCompactSurfaceGraphWeight coarseLaw.bundleClass
        coarseLaw.distinguishedRegion data.fineOrdinaryRegionWeight
          data.fineTwistedRegionWeight field
        ∂normalizedCompactHaarFiniteProductMeasure (Edge := FineEdge) (G := CoverGroup) ∧
    data.finePartitionFunction ≠ 0 ∧ data.finePartitionFunction ≠ ⊤ :=
  ⟨data.finePartitionFunction_eq_lintegral,
    data.finePartitionFunction_ne_zero, data.finePartitionFunction_ne_top⟩

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
include data in
/-- The curve family cannot disappear in the split-bond graph interface. -/
theorem curve_family_nonempty : Nonempty Curve :=
  data.curveRefinement.curve_nonempty

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
/-- The exact fine weighted graph measure pushes to the coarse one for each region. -/
theorem exact_weighted_pushforward (region : Region) :
    Measure.map (data.curveRefinement.graph.configurationMap (G := CoverGroup))
      (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
        data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) =
    senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
      coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight :=
  data.exact_graphMeasure_pushforward region

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
/-- The fine equation-(8.3) measure is normalized and nonzero, rather than an empty surrogate. -/
theorem fine_measure_nonvacuity (region : Region) :
    senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
      data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight Set.univ = 1 ∧
    senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
      data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight ≠ 0 :=
  ⟨data.fineGraphMeasure_univ region, data.fineGraphMeasure_ne_zero region⟩

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
/-- The unchanged stochastic finite law is represented on the split-bond fine graph. -/
theorem exact_fine_finite_law (region : Region) :
    Measure.map coarseLaw.sampleHolonomy coarseLaw.sampleMeasure =
      Measure.map (senguptaFiniteGraphHolonomy coarseLaw.projection fineCurveWord)
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) :=
  data.finiteDimensionalLaw_on_fineGraph region

omit [T2Space CoverGroup] [MeasurableMul₂ CoverGroup] [MeasurableInv CoverGroup]
    [Fintype Curve] [Nonempty Curve] [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
/-- Hostile measure probe: changing the required coarse pushforward is rejected. -/
theorem changed_weighted_pushforward_blocked (region : Region)
    (changed : Measure.map
        (data.curveRefinement.graph.configurationMap (G := CoverGroup))
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight) ≠
      senguptaCompactSurfaceGraphMeasure coarseLaw.partitionFunction coarseLaw.bundleClass region
        coarseLaw.ordinaryRegionWeight coarseLaw.twistedRegionWeight) : False :=
  changed (data.graphMeasure_pushforward region)

omit [T2Space CoverGroup] [Fintype Curve] [Nonempty Curve]
    [DecidableEq CoarseEdge] [DecidableEq FineEdge] in
/-- Hostile law probe: a different fine projected curve law cannot use this exact refinement. -/
theorem changed_fine_law_blocked (region : Region)
    (changed : Measure.map coarseLaw.sampleHolonomy coarseLaw.sampleMeasure ≠
      Measure.map (senguptaFiniteGraphHolonomy coarseLaw.projection fineCurveWord)
        (senguptaCompactSurfaceGraphMeasure data.finePartitionFunction coarseLaw.bundleClass region
          data.fineOrdinaryRegionWeight data.fineTwistedRegionWeight)) : False :=
  changed (data.finiteDimensionalLaw_on_fineGraph region)

end

end YangMills.Dimensions.TwoDimensionalSenguptaCurveBondGraphMeasureRefinement.Probes
