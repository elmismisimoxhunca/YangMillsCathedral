/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGeneralBoundaryExpectationLaw

/-!
# Probes for the general boundary-choice expectation law

The probes distinguish pointwise choice dependence from derived integral independence and pin exact
densities, carriers, ambient interpretation, normalization, same-law indexing, and dimension.
-/

namespace YangMills.Dimensions.TwoDimensionalGeneralBoundaryExpectationLaw.Probes

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
    (data : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- One choice uses unchanged densities at exact areas and its exact ordered boundary holonomies. -/
theorem exact_choice_density
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) (configuration : embedded.Edge → G) :
    generalBoundarySelectedFaceDensityProduct (law := law) choice configuration =
      ∏ face : embedded.Face,
        law.selectedAreaDensity (embedded.faceArea face)
          (TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
            (G := G) (H := G) choice face configuration) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Each choice carrier is exact normalized product Haar with its own density product. -/
theorem exact_choice_weight_measure
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    generalBoundarySelectedFaceWeightMeasure (law := law) choice =
      (normalizedCompactHaarFiniteProductMeasure embedded.Edge G).withDensity
        (generalBoundarySelectedFaceDensityProduct (law := law) choice) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Eligibility requires integrability against every exact boundary choice, not only one. -/
theorem exact_all_choice_integrability
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices)) :
    ∀ choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded),
      Integrable observable (generalBoundarySelectedFaceWeightMeasure (law := law) choice) :=
  observable.integrable_toFun

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Eligibility uses Driver's exact restricted gauge group fixing the supplied origin vertex. -/
theorem exact_restricted_gauge_invariance
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (gauge : embedded.Vertex → G) (fixes_origin : choices.FixesDriverOrigin gauge)
    (configuration : embedded.Edge → G) :
    observable (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget gauge configuration) =
      observable configuration :=
  observable.restricted_gauge_invariant gauge fixes_origin configuration

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Gauges not fixing the root are deliberately outside Definition 6.3; pointwise invariance is not
silently strengthened. -/
theorem unrestricted_gauge_difference_not_contradictory
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (gauge : embedded.Vertex → G)
    (does_not_fix_origin : ¬ choices.FixesDriverOrigin gauge)
    (configuration : embedded.Edge → G)
    (different : observable
      (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget gauge configuration) ≠
        observable configuration) :
    ¬ choices.FixesDriverOrigin gauge ∧
      observable (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget gauge configuration) ≠
        observable configuration :=
  ⟨does_not_fix_origin, different⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Failure of integrability for one choice blocks eligibility. -/
theorem one_choice_nonintegrability_blocked
    (f : (embedded.Edge → G) → ℂ)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (fails : ¬ Integrable f (generalBoundarySelectedFaceWeightMeasure (law := law) choice))
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (same_function : observable.toFun = f) : False := by
  apply fails
  simpa [same_function] using observable.integrable_toFun choice

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every eligible function has one unchanged ambient-path interpretation. -/
theorem exact_ambient_interpretation
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices)) (connection : Connection) :
    base.observable (data.physicalObservable observable) connection =
      observable (fun edge => base.holonomy (embedded.edgePath edge) connection) :=
  data.physicalObservable_eq_graphFunction observable connection

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every exact boundary choice computes the same original gauge-fixed expectation. -/
theorem exact_choice_expectation
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    base.expectation (data.physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) choice) :=
  data.expectation_eq_choiceIntegral observable choice

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integral-level choice independence is derived, not supplied separately. -/
theorem exact_derived_choice_independence
    (data : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup)
    (observable : GeneralBoundaryGaugeInvariantGraphObservable
      (G := G) (law := law) (choices := choices))
    (first second : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    (∫ configuration, observable configuration
      ∂(generalBoundarySelectedFaceWeightMeasure (law := law) first)) =
      ∫ configuration, observable configuration
        ∂(generalBoundarySelectedFaceWeightMeasure (law := law) second) :=
  TwoDimensionalGeneralBoundaryExpectationLawData.choiceIntegral_independent
    data observable first second

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A wrong choice-specific face product is rejected whenever observably distinct. -/
theorem wrong_choice_product_blocked
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded))
    (configuration : embedded.Edge → G) (wrong : ENNReal)
    (different : wrong ≠ ∏ face : embedded.Face,
      law.selectedAreaDensity (embedded.faceArea face)
        (TwoDimensionalGeneralBoundaryChoiceData.boundaryHolonomy
          (G := G) (H := G) choice face configuration))
    (claimed : generalBoundarySelectedFaceDensityProduct (law := law) choice configuration = wrong) :
    False := by
  apply different
  rw [← claimed]
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every choice-indexed carrier is normalized and nonzero by the shared exact unit observable. -/
theorem exact_choice_normalization
    (data : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) semigroup)
    (choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := embedded)) :
    generalBoundarySelectedFaceWeightMeasure (law := law) choice Set.univ = 1 ∧
      generalBoundarySelectedFaceWeightMeasure (law := law) choice ≠ 0 :=
  ⟨TwoDimensionalGeneralBoundaryExpectationLawData.faceWeightMeasure_univ data choice,
    TwoDimensionalGeneralBoundaryExpectationLawData.faceWeightMeasure_ne_zero data choice⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The constructor remains indexed by a convolution semigroup for the same selected density law. -/
theorem exact_same_law_semigroup_index
    (sameSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (sameData : TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) sameSemigroup) :
    Nonempty (TwoDimensionalGeneralBoundaryExpectationLawData
      (G := G) (choices := choices) sameSemigroup) :=
  ⟨sameData⟩

/-- General boundary-choice evidence remains strictly two-dimensional. -/
theorem general_boundary_expectation_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalGeneralBoundaryExpectationLaw.Probes
