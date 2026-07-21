/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryExpectationLaw
import YangMills.Mathematics.FiniteGraphTree

/-!
# Driver tree-freezing for the general planar boundary law

This module adds the remaining tree-freezing clause of Driver Theorem 6.4. A tree is any underlying-
edge subset satisfying Definition 5.1's no nonempty closed distinct-edge path condition; it need not
be connected or spanning. For every such tree, the reference product uses identity Dirac mass on
tree coordinates and unchanged normalized Haar elsewhere. The same choice-indexed face density and
the same ambient observable expectation are retained.

The law universally quantifies over all exact valid boundary presentations, eligible restricted-
gauge-invariant observables, and Driver trees. Equality of frozen and unfrozen integrals and frozen
carrier normalization are derived. No tree, graph, density, measure instance, or Yang--Mills theory
is constructed.
-/

namespace YangMills.Dimensions

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

/-- Exact choice-indexed face-weight carrier after freezing every tree coordinate to the identity. -/
noncomputable def generalBoundaryTreeFrozenFaceWeightMeasure
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge) : Measure (embedded.Edge → G) :=
  (finiteTreeFrozenProductMeasure embedded.Edge G tree).withDensity
    (generalBoundarySelectedFaceDensityProduct (law := law) choice)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The empty tree recovers the exact unfrozen face-weight carrier. -/
theorem generalBoundaryTreeFrozenFaceWeightMeasure_empty
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice ∅ =
      generalBoundarySelectedFaceWeightMeasure (law := law) choice := by
  rw [generalBoundaryTreeFrozenFaceWeightMeasure,
    generalBoundarySelectedFaceWeightMeasure,
    finiteTreeFrozenProductMeasure_empty]

/-- Source-facing universal tree-freezing strengthening of Driver Theorem 6.4. -/
structure TwoDimensionalGeneralBoundaryTreeFreezingLawData
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    (generalLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup) where
  treeFrozen_integrable : ∀
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge),
    FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree →
      Integrable observable
        (generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree)
  expectation_eq_treeFrozenChoiceIntegral : ∀
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge),
    FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree →
      base.expectation (generalLaw.physicalObservable observable) =
        ∫ configuration, observable configuration
          ∂(generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree)

namespace TwoDimensionalGeneralBoundaryTreeFreezingLawData

variable
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {generalLaw : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup}

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every Driver tree gives the same integral as the original unfrozen choice carrier. -/
theorem treeFrozenIntegral_eq_unfrozen
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    (∫ configuration, observable configuration
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree)) =
      ∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) choice) := by
  rw [← data.expectation_eq_treeFrozenChoiceIntegral observable choice tree isTree,
    ← generalLaw.expectation_eq_choiceIntegral observable choice]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Tree-frozen integrals are independent of both boundary presentation and Driver tree. -/
theorem treeFrozenIntegral_independent
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
          (law := law) secondChoice secondTree) := by
  rw [← data.expectation_eq_treeFrozenChoiceIntegral
      observable firstChoice firstTree firstIsTree,
    ← data.expectation_eq_treeFrozenChoiceIntegral
      observable secondChoice secondTree secondIsTree]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The unit observable derives normalization of every exact tree-frozen weighted carrier. -/
theorem treeFrozenWeightMeasure_univ
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree Set.univ = 1 := by
  have formula := data.expectation_eq_treeFrozenChoiceIntegral
    generalLaw.unitObservable choice tree isTree
  have left_eq_one :
      base.expectation (generalLaw.physicalObservable generalLaw.unitObservable) = 1 := by
    rw [TwoDimensionalGaugeFixedHolonomyMeasureData.expectation]
    calc
      (∫ ω, base.observable (generalLaw.physicalObservable generalLaw.unitObservable)
          (base.sampleConnection ω) ∂base.probabilityMeasure) =
          ∫ _ω, (1 : ℂ) ∂base.probabilityMeasure := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [generalLaw.physicalObservable_eq_graphFunction, generalLaw.unit_graphFunction]
      _ = 1 := by
        rw [integral_const, Measure.real_def, base.probability_normalized]
        simp
  have right_eq_one :
      (∫ configuration, generalLaw.unitObservable configuration
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree)) = 1 := by
    rw [← formula]
    exact left_eq_one
  have constant_integral :
      (∫ _configuration : embedded.Edge → G, (1 : ℂ)
        ∂(generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree)) = 1 := by
    convert right_eq_one using 1
    apply integral_congr_ae
    filter_upwards with configuration
    exact (generalLaw.unit_graphFunction configuration).symm
  rw [integral_const] at constant_integral
  have toReal_eq_one :
      (generalBoundaryTreeFrozenFaceWeightMeasure
        (law := law) choice tree Set.univ).toReal = 1 := by
    simpa [Measure.real_def] using congrArg Complex.re constant_integral
  exact (ENNReal.toReal_eq_one_iff _).mp toReal_eq_one

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every tree-frozen weighted carrier is nonzero by derived normalization. -/
theorem treeFrozenWeightMeasure_ne_zero
    (data : TwoDimensionalGeneralBoundaryTreeFreezingLawData generalLaw)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (tree : Finset embedded.Edge)
    (isTree : FiniteGraphEdgeSetIsTree embedded.edgeSource embedded.edgeTarget tree) :
    generalBoundaryTreeFrozenFaceWeightMeasure (law := law) choice tree ≠ 0 := by
  intro zero_measure
  have normalized := data.treeFrozenWeightMeasure_univ choice tree isTree
  rw [zero_measure] at normalized
  simp at normalized

end TwoDimensionalGeneralBoundaryTreeFreezingLawData

end

end YangMills.Dimensions
