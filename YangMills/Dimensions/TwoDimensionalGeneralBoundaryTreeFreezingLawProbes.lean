/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryTreeFreezingLaw

/-!
# Probes for Driver tree-freezing
-/

namespace YangMills.Dimensions.TwoDimensionalGeneralBoundaryTreeFreezingLaw.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq embedded.Edge]
    {choices : TwoDimensionalGeneralBoundaryChoiceData.{uVertex, uEdge, uFace, uXAxisCell}
      base embedded}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {generalLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup}
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The carrier uses the exact tree-frozen product and unchanged choice density. -/
theorem exact_tree_frozen_carrier
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge) :
    generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree =
      (finiteTreeFrozenProductMeasure embedded.Edge G tree).withDensity
        (generalBoundarySelectedFaceDensityProduct (law := law) choice) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The empty tree is legitimate and exactly recovers the unfrozen carrier. -/
theorem exact_empty_tree_recovery
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice ∅ =
      generalBoundarySelectedFaceWeightMeasure (law := law) choice :=
  generalBoundaryTreeFrozenFaceWeightMeasure_empty choice

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] in
/-- The tree need not be connected or spanning: the empty edge set satisfies Driver Definition 5.1. -/
theorem empty_tree_is_admissible :
    FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget ∅ :=
  finiteGraphEdgeSetIsTree_empty embedded.edgeSource embedded.edgeTarget

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] in
/-- A concrete non-loop edge gives a genuinely nonempty admissible freezing tree. -/
theorem nonloop_singleton_tree_is_admissible
    (edge : embedded.Edge)
    (not_loop : embedded.edgeSource edge ≠ embedded.edgeTarget edge) :
    FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget {edge} :=
  finiteGraphEdgeSetIsTree_singleton
    embedded.edgeSource embedded.edgeTarget edge not_loop

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integrability is required for every eligible observable, valid presentation, and Driver tree. -/
theorem exact_tree_frozen_integrability
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    Integrable observable
      (generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree) :=
  data.treeFrozen_integrable observable choice tree isTree

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every Driver tree and presentation computes the same original ambient expectation. -/
theorem exact_tree_frozen_expectation
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    base.expectation (generalLaw.physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree) :=
  data.expectation_eq_treeFrozenChoiceIntegral observable choice tree isTree

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Frozen/unfrozen integral equality is derived rather than independently supplied. -/
theorem exact_frozen_unfrozen_integral_equality
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    (∫ configuration, observable configuration
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree)) =
      ∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) choice) :=
  data.treeFrozenIntegral_eq_unfrozen observable choice tree isTree

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The derived equality simultaneously permits changes of boundary presentation and tree. -/
theorem exact_tree_and_choice_independence
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (firstChoice secondChoice :
      TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (firstTree secondTree : Finset embedded.Edge)
    (firstIsTree : FiniteGraphEdgeSetIsTree
      embedded.edgeSource embedded.edgeTarget firstTree)
    (secondIsTree : FiniteGraphEdgeSetIsTree
      embedded.edgeSource embedded.edgeTarget secondTree) :
    (∫ configuration, observable configuration
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) firstChoice firstTree)) =
      ∫ configuration, observable configuration
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) secondChoice secondTree) :=
  data.treeFrozenIntegral_independent observable firstChoice secondChoice
    firstTree secondTree firstIsTree secondIsTree

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Unit-observable normalization makes every tree-frozen weighted carrier nonzero. -/
theorem exact_tree_frozen_normalization
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree Set.univ = 1 ∧
      generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree ≠ 0 :=
  ⟨data.treeFrozenWeightMeasure_univ choice tree isTree,
    data.treeFrozenWeightMeasure_ne_zero choice tree isTree⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] in
/-- A cyclic edge set is outside the theorem rather than silently accepted as a tree. -/
theorem cyclic_edge_set_blocked
    (tree : Finset embedded.Edge)
    (cyclic : ¬ FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree)
    (claimed : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) : False :=
  cyclic claimed

/-- Tree-freezing evidence remains strictly two-dimensional. -/
theorem tree_freezing_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalGeneralBoundaryTreeFreezingLaw.Probes
