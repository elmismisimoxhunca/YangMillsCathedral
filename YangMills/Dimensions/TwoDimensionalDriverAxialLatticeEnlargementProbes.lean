/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialLatticeEnlargement

namespace YangMills.Dimensions.TwoDimensionalDriverAxialLatticeEnlargement.Probes

open Set
open YangMills.Mathematics

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge] {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    {axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)}
    {coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse)}
    {enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged)}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The continuum and lattice enlargement routes use literally equal oriented words. -/
theorem exact_refinement_square
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing) (edge : coarse.Edge) :
    (data.fineRefinement spacing).combinatorial.edgeWord
        (coarseApproximation.edgeMap spacing edge) =
      mapOrientedWord (enlargedApproximation.edgeMap spacing)
        (axial.refinement.combinatorial.edgeWord edge) :=
  data.refinementWord_commutes spacing edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Boundary transport remains face-indexed, so colliding face labels impose no cross-presentation
word equality. -/
theorem exact_facewise_boundary_transport
    (_data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (presentation : GeneralBoundaryPresentation enlarged) :
    (enlargedApproximation.boundaryPresentationMap spacing presentation).face =
        enlargedApproximation.faceMap spacing presentation.face ∧
      (enlargedApproximation.boundaryPresentationMap spacing presentation).components.map
          GeneralBoundaryComponentPresentation.word =
        presentation.components.map (fun component =>
          mapOrientedWord (enlargedApproximation.edgeMap spacing) component.word) :=
  ⟨enlargedApproximation.boundaryPresentation_face spacing presentation,
    enlargedApproximation.boundary_words_map spacing presentation⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every and only fine vertical/x-axis tree edge comes from the exact continuum tree. -/
theorem exact_tree_image
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (edge : (enlargedApproximation.fine spacing).Edge) :
    edge ∈ data.fineTree spacing ↔
      ∃ continuumEdge ∈ axial.tree,
        enlargedApproximation.edgeMap spacing continuumEdge = edge :=
  data.fineTree_image spacing edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The tree cannot be replaced by an arbitrary non-geometric edge set. -/
theorem exact_fine_tree_geometry
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (edge : (enlargedApproximation.fine spacing).Edge) :
    edge ∈ data.fineTree spacing ↔
      TwoDimensionalEmbeddedEdgeIsVertical edge ∨
        TwoDimensionalEmbeddedEdgeIsOnXAxis edge :=
  TwoDimensionalDriverAxialLatticeEnlargementData.fineTree_exact
    axial coarseApproximation enlargedApproximation data spacing edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- No unrelated `VB(ε)` edge can alter the product face integral. -/
theorem exact_fine_edge_coverage
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (edge : (enlargedApproximation.fine spacing).Edge) :
    (∃ coarseFineEdge : (coarseApproximation.fine spacing).Edge,
      ∃ oriented ∈ (data.fineRefinement spacing).combinatorial.edgeWord coarseFineEdge,
        OrientedEdge.underlying oriented = edge) ∨ edge ∈ data.fineTree spacing :=
  TwoDimensionalDriverAxialLatticeEnlargementData.fineEdge_covered
    axial coarseApproximation enlargedApproximation data spacing edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact square-lattice holonomy restriction commutes before applying every coarse observable. -/
theorem exact_lattice_observable_square
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (observable : (coarse.Edge → G) → ℝ)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    observable (coarseApproximation.coarseRestriction spacing configuration) =
      observable (axial.coarseRestriction
        (enlargedApproximation.coarseRestriction spacing configuration)) :=
  TwoDimensionalDriverAxialLatticeEnlargementData.observableRestriction_commutes
    axial coarseApproximation enlargedApproximation data spacing observable configuration

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- A disconnected second restriction route is hostilely rejected. -/
theorem wrong_lattice_restriction_blocked
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (wrong : coarseApproximation.coarseRestriction spacing configuration ≠
      axial.coarseRestriction
        (enlargedApproximation.coarseRestriction spacing configuration)) : False :=
  wrong (data.latticeRestriction_commutes spacing configuration)

end

end YangMills.Dimensions.TwoDimensionalDriverAxialLatticeEnlargement.Probes
