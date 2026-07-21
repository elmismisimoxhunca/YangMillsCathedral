/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialEnlargement
import YangMills.Dimensions.TwoDimensionalLatticeApproximatingHolonomy

/-!
# Driver's compatible lattice enlargement `B(ε) → VB(ε)`

The proofs of Driver Theorems 8.5 and 8.10 do not use an arbitrary approximation of `B` alone.
They enlarge every `B(ε)` to `VB(ε)`, require this family to approximate the exact continuum
`VB`, freeze precisely the vertical/x-axis tree `T(ε)`, and use one commuting restriction square.
This uninhabited interface records that proof-required geometry and exact lattice holonomy
compatibility. It states no measure identity or convergence theorem.
-/

namespace YangMills.Dimensions

open Set
open YangMills.Mathematics

noncomputable section

universe uG uGauge uSample uConnection
  uVertex uEdge uFace uXAxisCell
  uLargeVertex uLargeEdge uLargeFace uLargeXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell
  uFineLargeVertex uFineLargeEdge uFineLargeFace uFineLargeXAxisCell

attribute [local instance]
  TwoDimensionalLatticeApproximatingSequenceData.fineEdgeDecidableEq

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]
    (axial : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (coarseApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge,
      uFace, uXAxisCell, uFineVertex, uFineEdge, uFineFace, uFineXAxisCell}
      (base := base) (coarse := coarse))
    (enlargedApproximation : TwoDimensionalLatticeApproximatingHolonomyData.{uLargeVertex,
      uLargeEdge, uLargeFace, uLargeXAxisCell, uFineLargeVertex, uFineLargeEdge,
      uFineLargeFace, uFineLargeXAxisCell} (base := base) (coarse := enlarged))

/-- Exact proof geometry relating `B(ε)`, `VB(ε)`, `B`, and `VB`. -/
structure TwoDimensionalDriverAxialLatticeEnlargementData where
  fineRefinement : ∀ spacing,
    TwoDimensionalEmbeddedGraphRefinementData
      (G := G) (coarse := coarseApproximation.fine spacing)
      (fine := enlargedApproximation.fine spacing)
  fineBoundaryConnected : ∀ spacing,
    TwoDimensionalBoundaryConnectedPlanarGraphData base
      (enlargedApproximation.fine spacing)
  fineTree : ∀ spacing, Finset (enlargedApproximation.fine spacing).Edge
  fineTree_is_driver : ∀ spacing,
    FiniteGraphEdgeSetIsTree
      (enlargedApproximation.fine spacing).edgeSource
      (enlargedApproximation.fine spacing).edgeTarget
      (fineTree spacing)
  fineTree_mem_iff_vertical_or_xAxis : ∀ spacing edge,
    edge ∈ fineTree spacing ↔
      TwoDimensionalEmbeddedEdgeIsVertical edge ∨
        TwoDimensionalEmbeddedEdgeIsOnXAxis edge
  /-- `T(ε)` is exactly the image of the continuum vertical/x-axis tree. -/
  fineTree_image : ∀ spacing edge,
    edge ∈ fineTree spacing ↔
      ∃ continuumEdge ∈ axial.tree,
        enlargedApproximation.edgeMap spacing continuumEdge = edge
  /-- The two refinement routes from `B` to `VB(ε)` use literally the same oriented edge word. -/
  refinementWord_commutes : ∀ spacing edge,
    (fineRefinement spacing).combinatorial.edgeWord
        (coarseApproximation.edgeMap spacing edge) =
      mapOrientedWord (enlargedApproximation.edgeMap spacing)
        (axial.refinement.combinatorial.edgeWord edge)
  /-- No edge of `VB(ε)` is unrelated to both a `B(ε)` subdivision and `T(ε)`. -/
  fineEdge_coarseSubdivision_or_tree : ∀ spacing edge,
    (∃ coarseFineEdge : (coarseApproximation.fine spacing).Edge,
      ∃ oriented ∈ (fineRefinement spacing).combinatorial.edgeWord coarseFineEdge,
        OrientedEdge.underlying oriented = edge) ∨
      edge ∈ fineTree spacing
  /-- Exact square-lattice word evaluation commutes with both routes to the original graph `B`. -/
  latticeRestriction_commutes : ∀ spacing
      (configuration : EpsilonSquareLatticeAxialConfiguration G spacing),
    coarseApproximation.coarseRestriction spacing configuration =
      axial.coarseRestriction
        (enlargedApproximation.coarseRestriction spacing configuration)

namespace TwoDimensionalDriverAxialLatticeEnlargementData

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every fine enlarged edge is accounted for by the fine coarse graph or the exact axial tree. -/
theorem fineEdge_covered
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (edge : (enlargedApproximation.fine spacing).Edge) :
    (∃ coarseFineEdge : (coarseApproximation.fine spacing).Edge,
      ∃ oriented ∈ (data.fineRefinement spacing).combinatorial.edgeWord coarseFineEdge,
        OrientedEdge.underlying oriented = edge) ∨
      edge ∈ data.fineTree spacing :=
  data.fineEdge_coarseSubdivision_or_tree spacing edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The distinguished fine tree has exactly Driver's geometric scope. -/
theorem fineTree_exact
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (edge : (enlargedApproximation.fine spacing).Edge) :
    edge ∈ data.fineTree spacing ↔
      TwoDimensionalEmbeddedEdgeIsVertical edge ∨
        TwoDimensionalEmbeddedEdgeIsOnXAxis edge :=
  data.fineTree_mem_iff_vertical_or_xAxis spacing edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Observable pullback is identical along the two exact restriction routes. -/
theorem observableRestriction_commutes
    (data : TwoDimensionalDriverAxialLatticeEnlargementData
      axial coarseApproximation enlargedApproximation)
    (spacing : PositiveLatticeSpacing)
    (observable : (coarse.Edge → G) → ℝ)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    observable (coarseApproximation.coarseRestriction spacing configuration) =
      observable (axial.coarseRestriction
        (enlargedApproximation.coarseRestriction spacing configuration)) := by
  rw [data.latticeRestriction_commutes spacing configuration]

end TwoDimensionalDriverAxialLatticeEnlargementData

end

end YangMills.Dimensions
