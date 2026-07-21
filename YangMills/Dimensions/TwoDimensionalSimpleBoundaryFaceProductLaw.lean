/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSimpleBoundaryPlanarGraph
import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup
import YangMills.Mathematics.FiniteOrientedEdgeFaceWeight

/-!
# Simple-boundary planar face-product expectation law

This module states the source-facing expectation layer for the exact topological Jordan-boundary
subclass already formalized. It uses the unchanged selected-loop density family at each exact face
area and the exact finite product Haar carrier. Graph observables are explicitly finite-graph
supported, vertex-gauge invariant, measurable and integrable, and are tied pointwise to existing
ambient physical observables through holonomy of the same selected edge paths.

The face-product expectation is required acceptance data, not proved or inhabited. A canonical unit
member derives normalization of the exact weighted carrier; normalization is not accepted as a
second disconnected field. This is a restricted simple-boundary form of Driver's Theorem 6.6, not
the full bridge-multiplicity BC theorem and not the general cut-choice theorem 6.4.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uG uGauge uSample uConnection uVertex uEdge uFace uXAxisCell

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}

/-- Exact finite density product obtained by evaluating the unchanged selected-loop family at every
exact face area and boundary word. -/
noncomputable def simpleBoundarySelectedFaceDensityProduct
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base)
    (configuration : graph.Edge → G) : ENNReal :=
  finiteOrientedFaceDensityProduct graph.Face law.selectedAreaDensity
    graph.faceArea graph.boundaryWord configuration

/-- The selected face-density product is measurable, derived from positive exact face areas and the
existing positive-time density measurability. -/
theorem simpleBoundarySelectedFaceDensityProduct_measurable
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) :
    Measurable (simpleBoundarySelectedFaceDensityProduct (law := law) graph) := by
  apply finiteOrientedFaceDensityProduct_measurable
  intro face
  exact law.selectedAreaDensity_measurable
    (graph.faceArea face) (graph.faceArea_pos face)

/-- Exact product-Haar carrier weighted by the unchanged selected density at every exact face. -/
noncomputable def simpleBoundarySelectedFaceWeightMeasure
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) :
    Measure (graph.Edge → G) :=
  finiteOrientedFaceWeightMeasure graph.Edge graph.Face G law.selectedAreaDensity
    graph.faceArea graph.boundaryWord

/-- Every eligible complex graph function: measurable and integrable against the exact selected
face carrier, and invariant under every finite vertex gauge transformation. Quantifying over this
structure is universal over the full stated function class, rather than over a selected family. -/
structure SimpleBoundaryGaugeInvariantGraphObservable
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) where
  toFun : (graph.Edge → G) → ℂ
  measurable_toFun : Measurable toFun
  integrable_toFun : Integrable toFun
    (simpleBoundarySelectedFaceWeightMeasure (law := law) graph)
  gauge_invariant : ∀ gauge configuration,
    toFun (finiteEdgeGaugeAction graph.edgeSource graph.edgeTarget gauge configuration) =
      toFun configuration

instance (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) :
    CoeFun (SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph)
      (fun _ => (graph.Edge → G) → ℂ) :=
  ⟨SimpleBoundaryGaugeInvariantGraphObservable.toFun⟩

/-- Source-facing simple-boundary specialization of Driver's finite face-product expectation law,
universally quantified over all graph functions satisfying the stated measurability, integrability,
and finite vertex-gauge invariance hypotheses. -/
structure TwoDimensionalSimpleBoundaryFaceProductLawData
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) where
  /-- An eligible canonical constant-one member, used to derive normalization. -/
  unitObservable : SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph
  /-- Every eligible graph function is interpreted by one existing ambient physical observable. -/
  physicalObservable :
    SimpleBoundaryGaugeInvariantGraphObservable (law := law) graph →
      base.GaugeInvariantObservable
  /-- Exact ambient interpretation through holonomy of the same selected graph paths. -/
  physicalObservable_eq_graphFunction : ∀ observable connection,
    base.observable (physicalObservable observable) connection =
      observable (fun edge => base.holonomy (graph.edgePath edge) connection)
  /-- The designated unit member is exactly constant one. -/
  unit_graphFunction : ∀ configuration, unitObservable configuration = 1
  /-- Exact restricted Driver face-product expectation formula for every eligible function. -/
  expectation_eq_faceProduct : ∀ observable,
    base.expectation (physicalObservable observable) =
      ∫ configuration, observable configuration
        ∂(simpleBoundarySelectedFaceWeightMeasure (law := law) graph)

namespace TwoDimensionalSimpleBoundaryFaceProductLawData

variable
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {graph : TwoDimensionalSimpleBoundaryPlanarGraphData base}

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact weighted finite face carrier is normalized, derived by applying the face-product law
to the exact unit observable and using the original gauge-fixed probability normalization. -/
theorem faceWeightMeasure_univ
    (data : TwoDimensionalSimpleBoundaryFaceProductLawData semigroup graph) :
    simpleBoundarySelectedFaceWeightMeasure (law := law) graph Set.univ = 1 := by
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
        ∂(simpleBoundarySelectedFaceWeightMeasure (law := law) graph)) = 1 := by
    rw [← formula]
    exact left_eq_one
  have constant_integral :
      (∫ _configuration : graph.Edge → G, (1 : ℂ)
        ∂(simpleBoundarySelectedFaceWeightMeasure (law := law) graph)) = 1 := by
    convert right_eq_one using 1
    apply integral_congr_ae
    filter_upwards with configuration
    exact (data.unit_graphFunction configuration).symm
  rw [integral_const] at constant_integral
  have toReal_eq_one :
      (simpleBoundarySelectedFaceWeightMeasure (law := law) graph Set.univ).toReal = 1 := by
    simpa [Measure.real_def] using congrArg Complex.re constant_integral
  exact (ENNReal.toReal_eq_one_iff _).mp toReal_eq_one

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The derived normalization prevents the exact face carrier from being the zero measure. -/
theorem faceWeightMeasure_ne_zero
    (data : TwoDimensionalSimpleBoundaryFaceProductLawData semigroup graph) :
    simpleBoundarySelectedFaceWeightMeasure (law := law) graph ≠ 0 := by
  intro zero_measure
  have normalized := data.faceWeightMeasure_univ
  rw [zero_measure] at normalized
  simp at normalized

end TwoDimensionalSimpleBoundaryFaceProductLawData

end

end YangMills.Dimensions
