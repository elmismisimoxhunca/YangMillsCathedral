/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialEnlargement
import YangMills.Dimensions.TwoDimensionalGeneralBoundaryTreeFreezingLaw

/-!
# Driver's arbitrary-function heat expectation on `VB`

Equation (6.1) in Driver's proof of Theorem 6.6 applies Theorem 4.12, vertical-strip independence,
and x-axis reflection symmetry on the enlarged graph `VB`. Every bounded measurable function on the
coarse graph is pulled back through exact coarse restriction, while the enlarged vertical/x-axis tree
is frozen and every bounded face receives the unchanged area heat density.

This module states that source-facing bridge for the unchanged selected heat-density law. A future
outer contract must pair it with the common representation/Laplacian/heat chain indexed by that same
law. It is uninhabited and constructs no expectation law or lattice convergence.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

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
    (axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))

/-- Source-facing arbitrary-function identity (6.1) on Driver's exact enlarged graph. -/
structure TwoDimensionalDriverAxialEnlargedHeatExpectationData :
    Type (max (max uG uSample) (max uLargeEdge uLargeFace)) where
  choice : TwoDimensionalGeneralBoundaryChoiceData.Choice (embedded := enlarged)
  /-- Connected boundaries use exactly the canonical BC word, not an unrelated presentation. -/
  canonical_boundary_words : ∀ face,
    (choice.presentation face).components.map
        GeneralBoundaryComponentPresentation.word =
      [axial.enlargedBoundaryConnected.boundaryWord face]
  enlargedHeatMeasure_normalized :
    generalBoundaryTreeFrozenFaceWeightMeasure
      (law := law) choice axial.tree univ = 1
  expectation_eq_enlargedHeatIntegral :
    ∀ observable : (coarse.Edge → G) → ℝ,
      Measurable observable →
      (∃ bound : ℝ, ∀ configuration, |observable configuration| ≤ bound) →
      (∫ sample,
        observable (fun edge => base.holonomy (coarse.edgePath edge)
          (base.sampleConnection sample)) ∂base.probabilityMeasure) =
        ∫ configuration, observable (axial.coarseRestriction configuration)
          ∂generalBoundaryTreeFrozenFaceWeightMeasure
            (law := law) choice axial.tree

namespace TwoDimensionalDriverAxialEnlargedHeatExpectationData

/-- The enlarged integrand is measurably the exact coarse pullback. -/
theorem pulledObservable_measurable
    (_data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (observable : (coarse.Edge → G) → ℝ)
    (observable_measurable : Measurable observable) :
    Measurable (fun configuration : enlarged.Edge → G =>
      observable (axial.coarseRestriction configuration)) :=
  observable_measurable.comp axial.coarseRestriction_measurable

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact enlarged heat carrier cannot be zero. -/
theorem enlargedHeatMeasure_ne_zero
    (data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial) :
    generalBoundaryTreeFrozenFaceWeightMeasure
      (law := law) data.choice axial.tree ≠ 0 := by
  intro zeroMeasure
  have normalized := data.enlargedHeatMeasure_normalized
  rw [zeroMeasure] at normalized
  simp at normalized

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Ambient coarse observables used on the left are literally the restriction of enlarged ambient
holonomies used on the right. -/
theorem ambient_observable_coherence
    (_data : TwoDimensionalDriverAxialEnlargedHeatExpectationData (law := law) axial)
    (observable : (coarse.Edge → G) → ℝ) (connection : Connection) :
    observable (axial.coarseRestriction
      (fun edge => base.holonomy (enlarged.edgePath edge) connection)) =
      observable (fun edge => base.holonomy (coarse.edgePath edge) connection) := by
  rw [axial.ambient_coarseRestriction connection]

end TwoDimensionalDriverAxialEnlargedHeatExpectationData

end

end YangMills.Dimensions
