/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialEnlargedHeatExpectation

/-!
# Probes for Driver equation (6.1)
-/

namespace YangMills.Dimensions.TwoDimensionalDriverAxialEnlargedHeatExpectation.Probes

open MeasureTheory Set

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    {axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)}

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every enlarged face uses exactly its canonical connected BC boundary word. -/
theorem exact_canonical_boundary_words
    (data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (face : enlarged.Face) :
    (data.choice.presentation face).components.map
        GeneralBoundaryComponentPresentation.word =
      [axial.enlargedBoundaryConnected.boundaryWord face] :=
  data.canonical_boundary_words face

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Equation (6.1) covers every bounded measurable coarse real function through exact restriction. -/
theorem exact_arbitrary_function_expectation
    (data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (observable : (coarse.Edge → G) → ℝ)
    (measurable : Measurable observable)
    (bounded : ∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound) :
    (∫ sample,
      observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure) =
      ∫ configuration, observable (axial.coarseRestriction configuration)
        ∂generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) data.choice axial.tree :=
  data.expectation_eq_enlargedHeatIntegral observable measurable bounded

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact enlarged heat carrier is normalized and nonzero. -/
theorem exact_enlarged_heat_carrier
    (data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial) :
    generalBoundaryTreeFrozenFaceWeightMeasure
        (law := law) data.choice axial.tree univ = 1 ∧
      generalBoundaryTreeFrozenFaceWeightMeasure
        (law := law) data.choice axial.tree ≠ 0 :=
  ⟨data.enlargedHeatMeasure_normalized, data.enlargedHeatMeasure_ne_zero⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [DecidableEq coarse.Edge] in
/-- Constant one makes the arbitrary bounded measurable scope nonempty. -/
theorem constant_one_eligible :
    Measurable (fun _ : coarse.Edge → G => (1 : ℝ)) ∧
      ∃ bound : ℝ, ∀ configuration : coarse.Edge → G,
        |(fun _ : coarse.Edge → G => (1 : ℝ)) configuration| ≤ bound :=
  ⟨measurable_const, ⟨1, fun _ => by norm_num⟩⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Ambient factorization uses actual continuum holonomy compatibility. -/
theorem exact_ambient_factorization
    (data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (observable : (coarse.Edge → G) → ℝ) (connection : Connection) :
    observable (axial.coarseRestriction
      (fun edge => base.holonomy (enlarged.edgePath edge) connection)) =
      observable (fun edge => base.holonomy (coarse.edgePath edge) connection) :=
  TwoDimensionalDriverAxialEnlargedHeatExpectationData.ambient_observable_coherence
    axial data observable connection

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A wrong equation (6.1) value for one eligible observable is hostilely rejected. -/
theorem wrong_enlarged_expectation_blocked
    (data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (observable : (coarse.Edge → G) → ℝ)
    (measurable : Measurable observable)
    (bounded : ∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound)
    (claimed : (∫ sample,
      observable (fun edge => base.holonomy (coarse.edgePath edge)
        (base.sampleConnection sample)) ∂base.probabilityMeasure) ≠
      ∫ configuration, observable (axial.coarseRestriction configuration)
        ∂generalBoundaryTreeFrozenFaceWeightMeasure
          (law := law) data.choice axial.tree) : False :=
  claimed (data.expectation_eq_enlargedHeatIntegral observable measurable bounded)

end

end YangMills.Dimensions.TwoDimensionalDriverAxialEnlargedHeatExpectation.Probes
