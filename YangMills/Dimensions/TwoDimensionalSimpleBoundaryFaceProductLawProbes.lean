/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSimpleBoundaryFaceProductLaw

/-!
# Probes for the simple-boundary face-product law

The probes pin universal eligible-function coverage, the unchanged density family, exact graph
paths/areas/words, product Haar, finite vertex-gauge invariance, ambient interpretation, expectation,
unit-derived normalization, same-law semigroup indexing, and dimension separation.
-/

namespace YangMills.Dimensions.TwoDimensionalSimpleBoundaryFaceProductLaw.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {graph : TwoDimensionalSimpleBoundaryPlanarGraphData base}
    (data : TwoDimensionalSimpleBoundaryFaceProductLawData semigroup graph)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The face density product uses the exact unchanged selected density at every exact graph face. -/
theorem exact_selected_face_density (configuration : graph.Edge → G) :
    simpleBoundarySelectedFaceDensityProduct (law := law) graph configuration =
      ∏ face : graph.Face,
        law.selectedAreaDensity (graph.faceArea face)
          (finiteOrientedWordHolonomy configuration (graph.boundaryWord face)) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The weighted carrier unfolds to exact normalized product Haar with that same density product. -/
theorem exact_selected_face_weight_measure :
    simpleBoundarySelectedFaceWeightMeasure (law := law) graph =
      (normalizedCompactHaarFiniteProductMeasure graph.Edge G).withDensity
        (simpleBoundarySelectedFaceDensityProduct (law := law) graph) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Eligibility itself exposes measurable, integrable, and full finite-gauge-invariant hypotheses. -/
theorem exact_eligibility
    (observable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph) :
    Measurable observable ∧
      Integrable observable (simpleBoundarySelectedFaceWeightMeasure (law := law) graph) ∧
      ∀ gauge configuration,
        observable (finiteEdgeGaugeAction graph.edgeSource graph.edgeTarget gauge configuration) =
          observable configuration :=
  ⟨observable.measurable_toFun, observable.integrable_toFun, observable.gauge_invariant⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A nonintegrable graph function cannot masquerade as an eligible observable. -/
theorem nonintegrable_function_blocked
    (f : (graph.Edge → G) → ℂ)
    (not_integrable : ¬ Integrable f
      (simpleBoundarySelectedFaceWeightMeasure (law := law) graph))
    (observable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph)
    (same_function : observable.toFun = f) : False := by
  apply not_integrable
  simpa [same_function] using observable.integrable_toFun

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A function failing one finite vertex-gauge test cannot be admitted. -/
theorem nongaugeInvariant_function_blocked
    (f : (graph.Edge → G) → ℂ) (gauge : graph.Vertex → G)
    (configuration : graph.Edge → G)
    (fails : f (finiteEdgeGaugeAction graph.edgeSource graph.edgeTarget gauge configuration) ≠
      f configuration)
    (observable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph)
    (same_function : observable.toFun = f) : False := by
  apply fails
  rw [← same_function]
  exact observable.gauge_invariant gauge configuration

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every eligible graph function—not merely a selected or subsingleton family—receives the exact
ambient interpretation through the same graph paths. -/
theorem exact_ambient_interpretation
    (observable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph)
    (connection : Connection) :
    base.observable (data.physicalObservable observable) connection =
      observable (fun edge => base.holonomy (graph.edgePath edge) connection) :=
  data.physicalObservable_eq_graphFunction observable connection

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Driver's restricted face-product formula is universal over every eligible graph function. -/
theorem exact_faceProduct_expectation
    (observable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph) :
    base.expectation (data.physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(simpleBoundarySelectedFaceWeightMeasure (law := law) graph) :=
  data.expectation_eq_faceProduct observable

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A wrong density/area/word substitution is rejected whenever it changes the exact product. -/
theorem wrong_face_product_blocked
    (configuration : graph.Edge → G) (wrong : ENNReal)
    (different : wrong ≠ ∏ face : graph.Face,
      law.selectedAreaDensity (graph.faceArea face)
        (finiteOrientedWordHolonomy configuration (graph.boundaryWord face)))
    (claimed : simpleBoundarySelectedFaceDensityProduct (law := law) graph configuration = wrong) :
    False := by
  apply different
  rw [← claimed]
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A wrong edge-path interpretation is rejected whenever it changes one observable value. -/
theorem wrong_edge_paths_blocked
    (observable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph)
    (connection : Connection) (wrong : ℂ)
    (different : wrong ≠ observable
      (fun edge => base.holonomy (graph.edgePath edge) connection))
    (claimed : base.observable (data.physicalObservable observable) connection = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.physicalObservable_eq_graphFunction observable connection

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Normalization is derived from the exact unit member, not supplied independently. -/
theorem exact_derived_normalization
    (data : TwoDimensionalSimpleBoundaryFaceProductLawData semigroup graph) :
    simpleBoundarySelectedFaceWeightMeasure (law := law) graph Set.univ = 1 :=
  TwoDimensionalSimpleBoundaryFaceProductLawData.faceWeightMeasure_univ data

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact weighted carrier cannot collapse to the zero measure. -/
theorem zero_weighted_measure_blocked
    (data : TwoDimensionalSimpleBoundaryFaceProductLawData semigroup graph) :
    simpleBoundarySelectedFaceWeightMeasure (law := law) graph ≠ 0 :=
  TwoDimensionalSimpleBoundaryFaceProductLawData.faceWeightMeasure_ne_zero data

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The law constructor is indexed by a semigroup certificate for this same density law. -/
theorem exact_same_law_semigroup_index
    (sameSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (sameData : TwoDimensionalSimpleBoundaryFaceProductLawData sameSemigroup graph) :
    Nonempty (TwoDimensionalSimpleBoundaryFaceProductLawData sameSemigroup graph) :=
  ⟨sameData⟩

/-- This two-dimensional exact face formula cannot discharge a four-dimensional contract. -/
theorem two_dimensional_face_law_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSimpleBoundaryFaceProductLaw.Probes
