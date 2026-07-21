/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryChoice
import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup

/-!
# General planar boundary-choice expectation law

This module states the boundary-choice-independence clause of Driver Theorem 6.4 with every
disconnected-boundary presentation kept explicit.
For each exact choice, the weighted product-Haar integral uses the unchanged selected density at the
same geometric face area but at that choice's ordered component holonomy. The same ambient
observable expectation equals every such integral, from which integral-level choice independence is
derived. No false pointwise equality of boundary holonomies or density products is imposed.

The law uses Driver Definition 6.3's restricted gauge invariance: finite vertex gauges fix the
supplied origin vertex. It is uninhabited acceptance data and constructs no graph, cut system,
probability law, or Yang--Mills theory. The project's embedded-arc subdivision strengthening remains
explicit. The theorem's separate universal tree-freezing clause remains later work.
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

/-- Choice-indexed product of unchanged density values at exact geometric face areas. -/
noncomputable def generalBoundarySelectedFaceDensityProduct
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (configuration : embedded.Edge → G) : ENNReal :=
  ∏ face : embedded.Face,
    law.selectedAreaDensity (embedded.faceArea face)
      (TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
        (G := G) (H := G) choice face configuration)

/-- Every exact choice-indexed density product is measurable. -/
theorem generalBoundarySelectedFaceDensityProduct_measurable
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    Measurable (generalBoundarySelectedFaceDensityProduct (law := law) choice) := by
  unfold generalBoundarySelectedFaceDensityProduct
  simpa using
    Finset.measurable_prod Finset.univ (fun face _membership =>
      (law.selectedAreaDensity_measurable
        (embedded.faceArea face) (embedded.faceArea_pos face)).comp
          (TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy_measurable
            (G := G) choice face))

/-- Exact choice-indexed product-Haar carrier. -/
noncomputable def generalBoundarySelectedFaceWeightMeasure
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    Measure (embedded.Edge → G) :=
  (normalizedCompactHaarFiniteProductMeasure embedded.Edge G).withDensity
    (generalBoundarySelectedFaceDensityProduct (law := law) choice)

/-- Every eligible general-boundary graph function is measurable, restricted-gauge invariant in
Driver's rooted sense, and integrable against every choice-indexed exact carrier. -/
structure GeneralBoundaryGaugeInvariantGraphObservable where
  toFun : (embedded.Edge → G) → ℂ
  measurable_toFun : Measurable toFun
  integrable_toFun : ∀ choice :
      TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded),
    Integrable toFun (generalBoundarySelectedFaceWeightMeasure (law := law) choice)
  restricted_gauge_invariant : ∀ gauge,
    choices.FixesDriverOrigin gauge → ∀ configuration,
      toFun (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget gauge configuration) =
        toFun configuration

instance : CoeFun (GeneralBoundaryGaugeInvariantGraphObservable
    (G := G) (law := law) (choices := choices))
    (fun _ => (embedded.Edge → G) → ℂ) :=
  ⟨GeneralBoundaryGaugeInvariantGraphObservable.toFun⟩

/-- Source-facing boundary-choice-independence clause of Driver Theorem 6.4, indexed by the same
selected-density semigroup. The separate tree-freezing clause is not claimed here. -/
structure TwoDimensionalGeneralBoundaryExpectationLawData
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law) where
  unitObservable : GeneralBoundaryGaugeInvariantGraphObservable
    (G := G) (law := law) (choices := choices)
  physicalObservable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices) → base.GaugeInvariantObservable
  physicalObservable_eq_graphFunction : ∀ observable connection,
    base.observable (physicalObservable observable) connection =
      observable (fun edge => base.holonomy (embedded.edgePath edge) connection)
  unit_graphFunction : ∀ configuration, unitObservable configuration = 1
  expectation_eq_choiceIntegral : ∀
      (observable : GeneralBoundaryGaugeInvariantGraphObservable
        (G := G) (law := law) (choices := choices))
      (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)),
    base.expectation (physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) choice)

namespace TwoDimensionalGeneralBoundaryExpectationLawData

variable {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Driver's ambiguity is removed at integral level because every choice computes the same ambient
expectation. No pointwise boundary-holonomy equality is used. -/
theorem choiceIntegral_independent
    (data : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (first second : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    (∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) first)) =
      ∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) second) := by
  rw [← data.expectation_eq_choiceIntegral observable first,
    ← data.expectation_eq_choiceIntegral observable second]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Each exact choice-indexed weighted carrier is normalized, derived from the same unit observable. -/
theorem faceWeightMeasure_univ
    (data : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    generalBoundarySelectedFaceWeightMeasure (law := law) choice Set.univ = 1 := by
  have formula := data.expectation_eq_choiceIntegral data.unitObservable choice
  have left_eq_one : base.expectation (data.physicalObservable data.unitObservable) = 1 := by
    rw [TwoDimensionalGaugeFixedHolonomyMeasureData.expectation]
    calc
      (∫ ω, base.observable (data.physicalObservable data.unitObservable)
          (base.sampleConnection ω) ∂base.probabilityMeasure) =
          ∫ _ω, (1 : ℂ) ∂base.probabilityMeasure := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [data.physicalObservable_eq_graphFunction, data.unit_graphFunction]
      _ = 1 := by
        rw [integral_const, Measure.real_def, base.probability_normalized]
        simp
  have right_eq_one :
      (∫ configuration, data.unitObservable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) choice)) = 1 := by
    rw [← formula]
    exact left_eq_one
  have constant_integral :
      (∫ _configuration : embedded.Edge → G, (1 : ℂ)
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) choice)) = 1 := by
    convert right_eq_one using 1
    apply integral_congr_ae
    filter_upwards with configuration
    exact (data.unit_graphFunction configuration).symm
  rw [integral_const] at constant_integral
  have toReal_eq_one :
      (generalBoundarySelectedFaceWeightMeasure (law := law) choice Set.univ).toReal = 1 := by
    simpa [Measure.real_def] using congrArg Complex.re constant_integral
  exact (ENNReal.toReal_eq_one_iff _).mp toReal_eq_one

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every choice-indexed carrier is nonzero by derived normalization. -/
theorem faceWeightMeasure_ne_zero
    (data : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    generalBoundarySelectedFaceWeightMeasure (law := law) choice ≠ 0 := by
  intro zero_measure
  have normalized := faceWeightMeasure_univ data choice
  rw [zero_measure] at normalized
  simp at normalized

end TwoDimensionalGeneralBoundaryExpectationLawData

end

end YangMills.Dimensions
