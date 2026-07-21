/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalBoundaryConnectedPlanarGraph
import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup
import YangMills.Mathematics.FiniteOrientedEdgeFaceWeight

/-!
# Boundary-connected planar face-product expectation law

This module states Driver Theorem 6.6 on the project's strengthened embedded-arc BC certificate.
It universally quantifies over all measurable, integrable complex graph functions invariant under
every finite vertex gauge transformation. Each such function is tied pointwise to an existing
ambient physical observable through holonomy of the unchanged selected edge paths. Its expectation
is required to equal integration against one normalized Haar coordinate per underlying edge,
weighted by the product of the unchanged selected density at exact geometric face areas and exact
bridge-aware boundary words.

The law is uninhabited acceptance data. It constructs no graph, density, measure, process, or
Yang--Mills theory. Driver-permitted one-edge loop incidence still requires subdivision into this
project's embedded arcs. Theorem 6.4's general non-BC cut choices remain separate work.
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

/-- Exact BC face-density product using unchanged densities, exact areas, and bridge-aware words. -/
noncomputable def boundaryConnectedSelectedFaceDensityProduct
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded)
    (configuration : embedded.Edge → G) : ENNReal :=
  finiteOrientedFaceDensityProduct embedded.Face law.selectedAreaDensity
    embedded.faceArea
    (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph) configuration

/-- Measurability of the exact BC density product follows from positivity of geometric face areas
and the existing selected-density slice measurability. -/
theorem boundaryConnectedSelectedFaceDensityProduct_measurable
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded) :
    Measurable (boundaryConnectedSelectedFaceDensityProduct (law := law) graph) := by
  apply finiteOrientedFaceDensityProduct_measurable
  intro face
  exact law.selectedAreaDensity_measurable
    (embedded.faceArea face) (embedded.faceArea_pos face)

/-- Exact normalized product-Haar carrier weighted by the BC face-density product. -/
noncomputable def boundaryConnectedSelectedFaceWeightMeasure
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded) :
    Measure (embedded.Edge → G) :=
  finiteOrientedFaceWeightMeasure embedded.Edge embedded.Face G law.selectedAreaDensity
    embedded.faceArea (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph)

/-- Every eligible BC graph function, universally represented rather than selected from an arbitrary
observable family. -/
structure BoundaryConnectedGaugeInvariantGraphObservable
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded) where
  toFun : (embedded.Edge → G) → ℂ
  measurable_toFun : Measurable toFun
  integrable_toFun : Integrable toFun
    (boundaryConnectedSelectedFaceWeightMeasure (law := law) graph)
  gauge_invariant : ∀ gauge configuration,
    toFun (finiteEdgeGaugeAction embedded.edgeSource embedded.edgeTarget gauge configuration) =
      toFun configuration

instance (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded) :
    CoeFun (BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph)
      (fun _ => (embedded.Edge → G) → ℂ) :=
  ⟨BoundaryConnectedGaugeInvariantGraphObservable.toFun⟩

/-- Source-facing Driver Theorem 6.6 acceptance interface on the exact strengthened embedded BC
graph, requiring the same-law convolution semigroup certificate. -/
structure TwoDimensionalBoundaryConnectedFaceProductLawData
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded) where
  unitObservable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph
  physicalObservable : BoundaryConnectedGaugeInvariantGraphObservable (law := law) graph →
    base.GaugeInvariantObservable
  physicalObservable_eq_graphFunction : ∀ observable connection,
    base.observable (physicalObservable observable) connection =
      observable (fun edge => base.holonomy (embedded.edgePath edge) connection)
  unit_graphFunction : ∀ configuration, unitObservable configuration = 1
  expectation_eq_faceProduct : ∀ observable,
    base.expectation (physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(boundaryConnectedSelectedFaceWeightMeasure (law := law) graph)

namespace TwoDimensionalBoundaryConnectedFaceProductLawData

variable
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded}

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact normalization is derived from the constant-one observable and original gauge-fixed
probability normalization, never supplied as a disconnected field. -/
theorem faceWeightMeasure_univ
    (data : TwoDimensionalBoundaryConnectedFaceProductLawData semigroup graph) :
    boundaryConnectedSelectedFaceWeightMeasure (law := law) graph Set.univ = 1 := by
  have formula := data.expectation_eq_faceProduct data.unitObservable
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
        ∂(boundaryConnectedSelectedFaceWeightMeasure (law := law) graph)) = 1 := by
    rw [← formula]
    exact left_eq_one
  have constant_integral :
      (∫ _configuration : embedded.Edge → G, (1 : ℂ)
        ∂(boundaryConnectedSelectedFaceWeightMeasure (law := law) graph)) = 1 := by
    convert right_eq_one using 1
    apply integral_congr_ae
    filter_upwards with configuration
    exact (data.unit_graphFunction configuration).symm
  rw [integral_const] at constant_integral
  have toReal_eq_one :
      (boundaryConnectedSelectedFaceWeightMeasure (law := law) graph Set.univ).toReal = 1 := by
    simpa [Measure.real_def] using congrArg Complex.re constant_integral
  exact (ENNReal.toReal_eq_one_iff _).mp toReal_eq_one

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Derived normalization prevents collapse to the zero measure. -/
theorem faceWeightMeasure_ne_zero
    (data : TwoDimensionalBoundaryConnectedFaceProductLawData semigroup graph) :
    boundaryConnectedSelectedFaceWeightMeasure (law := law) graph ≠ 0 := by
  intro zero_measure
  have normalized := faceWeightMeasure_univ data
  rw [zero_measure] at normalized
  simp at normalized

end TwoDimensionalBoundaryConnectedFaceProductLawData

end

end YangMills.Dimensions
