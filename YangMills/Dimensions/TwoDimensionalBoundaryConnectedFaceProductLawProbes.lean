/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalBoundaryConnectedFaceProductLaw

/-!
# Probes for the boundary-connected face-product law

The probes pin universal eligible-function coverage, exact product Haar, unchanged density, exact
areas and bridge-aware words, ambient edge-path interpretation, normalization, same-law semigroup
indexing, hostile substitutions, and dimensional separation.
-/

namespace YangMills.Dimensions.TwoDimensionalBoundaryConnectedFaceProductLaw.Probes

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
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq embedded.Edge]
    {graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded}
    (data : TwoDimensionalBoundaryConnectedFaceProductLawData semigroup graph)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every factor uses the unchanged selected density at the exact area and bridge-aware word. -/
theorem exact_selected_face_density (configuration : embedded.Edge → G) :
    boundaryConnectedSelectedFaceDensityProduct (law := law) graph configuration =
      ∏ face : embedded.Face,
        law.selectedAreaDensity (embedded.faceArea face)
          (finiteOrientedWordHolonomy configuration
            (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face)) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact carrier is product normalized Haar weighted by that same density product. -/
theorem exact_selected_face_weight_measure :
    boundaryConnectedSelectedFaceWeightMeasure (law := law) graph =
      (normalizedCompactHaarFiniteProductMeasure embedded.Edge G).withDensity
        (boundaryConnectedSelectedFaceDensityProduct (law := law) graph) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every eligible function exposes measurability, exact-carrier integrability, and full vertex-gauge
invariance. -/
theorem exact_eligibility
    (observable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph) :
    Measurable observable ∧
      Integrable observable (boundaryConnectedSelectedFaceWeightMeasure (law := law) graph) ∧
      ∀ gauge configuration,
        observable (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget
          gauge configuration) = observable configuration :=
  ⟨observable.measurable_toFun, observable.integrable_toFun, observable.gauge_invariant⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A nonintegrable function cannot enter the universally quantified eligible carrier. -/
theorem nonintegrable_function_blocked
    (f : (embedded.Edge → G) → ℂ)
    (not_integrable : ¬ Integrable f
      (boundaryConnectedSelectedFaceWeightMeasure (law := law) graph))
    (observable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph)
    (same_function : observable.toFun = f) : False := by
  apply not_integrable
  simpa [same_function] using observable.integrable_toFun

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Failing one exact finite vertex-gauge test blocks eligibility. -/
theorem nongaugeInvariant_function_blocked
    (f : (embedded.Edge → G) → ℂ) (gauge : embedded.Vertex → G)
    (configuration : embedded.Edge → G)
    (fails : f (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget gauge configuration) ≠
      f configuration)
    (observable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph)
    (same_function : observable.toFun = f) : False := by
  apply fails
  rw [← same_function]
  exact observable.gauge_invariant gauge configuration

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every eligible function is tied to an existing ambient physical observable through unchanged
selected edge paths. -/
theorem exact_ambient_interpretation
    (observable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph)
    (connection : Connection) :
    base.observable (data.physicalObservable observable) connection =
      observable (fun edge => base.holonomy (embedded.edgePath edge) connection) :=
  data.physicalObservable_eq_graphFunction observable connection

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Driver Theorem 6.6 is required for every eligible graph function. -/
theorem exact_faceProduct_expectation
    (observable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph) :
    base.expectation (data.physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(boundaryConnectedSelectedFaceWeightMeasure (law := law) graph) :=
  data.expectation_eq_faceProduct observable

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Wrong density, area, or boundary-word substitutions are rejected when they alter the product. -/
theorem wrong_face_product_blocked
    (configuration : embedded.Edge → G) (wrong : ENNReal)
    (different : wrong ≠ ∏ face : embedded.Face,
      law.selectedAreaDensity (embedded.faceArea face)
        (finiteOrientedWordHolonomy configuration
          (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face)))
    (claimed : boundaryConnectedSelectedFaceDensityProduct (law := law) graph configuration = wrong) :
    False := by
  apply different
  rw [← claimed]
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A substituted ambient edge-path interpretation is rejected when observably distinct. -/
theorem wrong_edge_paths_blocked
    (observable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph)
    (connection : Connection) (wrong : ℂ)
    (different : wrong ≠ observable
      (fun edge => base.holonomy (embedded.edgePath edge) connection))
    (claimed : base.observable (data.physicalObservable observable) connection = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.physicalObservable_eq_graphFunction observable connection

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact carrier normalization is derived from the unit member. -/
theorem exact_derived_normalization
    (data : TwoDimensionalBoundaryConnectedFaceProductLawData semigroup graph) :
    boundaryConnectedSelectedFaceWeightMeasure (law := law) graph Set.univ = 1 :=
  TwoDimensionalBoundaryConnectedFaceProductLawData.faceWeightMeasure_univ data

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact weighted carrier cannot collapse to zero. -/
theorem zero_weighted_measure_blocked
    (data : TwoDimensionalBoundaryConnectedFaceProductLawData semigroup graph) :
    boundaryConnectedSelectedFaceWeightMeasure (law := law) graph ≠ 0 :=
  TwoDimensionalBoundaryConnectedFaceProductLawData.faceWeightMeasure_ne_zero data

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Construction is indexed by a convolution semigroup certificate for this same density law. -/
theorem exact_same_law_semigroup_index
    (sameSemigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (sameData : TwoDimensionalBoundaryConnectedFaceProductLawData sameSemigroup graph) :
    Nonempty (TwoDimensionalBoundaryConnectedFaceProductLawData sameSemigroup graph) :=
  ⟨sameData⟩

/-- A two-dimensional BC face law cannot discharge the four-dimensional Clay contract. -/
theorem boundary_connected_face_law_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalBoundaryConnectedFaceProductLaw.Probes
