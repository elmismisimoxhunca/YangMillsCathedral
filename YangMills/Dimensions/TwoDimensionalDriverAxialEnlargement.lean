/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalBoundaryConnectedPlanarGraph
import YangMills.Dimensions.TwoDimensionalGeneralBoundaryRefinementLaw

/-!
# Driver's axial enlargement `B → VB`

In the proof of Theorem 6.6 and again in §8, arbitrary coarse functions are handled only after
embedding the coarse graph `B` as exact subdivided paths in an enlarged boundary-connected graph
`VB`. The distinguished tree consists exactly of vertical edges and edges on the x-axis. This module
records that missing geometry and the exact measurable coarse restriction.

No strip independence, reflection law, expectation formula, or convergence theorem is asserted.
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

/-- An embedded edge is geometrically vertical throughout its exact path realization. -/
def TwoDimensionalEmbeddedEdgeIsVertical
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    (edge : embedded.Edge) : Prop :=
  ∃ x : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    twoDimensionalFirstCoordinate (embedded.pathCurve (embedded.edgePath edge) t) = x

/-- An embedded edge lies entirely on Driver's x-axis. -/
def TwoDimensionalEmbeddedEdgeIsOnXAxis
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    (edge : embedded.Edge) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    twoDimensionalSecondCoordinate (embedded.pathCurve (embedded.edgePath edge) t) = 0

variable
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]

/-- Exact source-facing geometry of Driver's enlarged graph `VB`. -/
structure TwoDimensionalDriverAxialEnlargementData where
  coarseBoundaryConnected : TwoDimensionalBoundaryConnectedPlanarGraphData base coarse
  enlargedBoundaryConnected : TwoDimensionalBoundaryConnectedPlanarGraphData base enlarged
  refinement : TwoDimensionalEmbeddedGraphRefinementData
    (G := G) (coarse := coarse) (fine := enlarged)
  tree : Finset enlarged.Edge
  tree_is_driver : FiniteGraphEdgeSetIsTree enlarged.edgeSource enlarged.edgeTarget tree
  tree_mem_iff_vertical_or_xAxis : ∀ edge,
    edge ∈ tree ↔
      TwoDimensionalEmbeddedEdgeIsVertical edge ∨
        TwoDimensionalEmbeddedEdgeIsOnXAxis edge
  /-- Every enlarged edge is either used by an exact coarse-edge subdivision or is one of the added
  vertical/x-axis tree edges. No unrelated extra edge may change the face geometry. -/
  enlargedEdge_coarseSubdivision_or_tree : ∀ edge : enlarged.Edge,
    (∃ coarseEdge : coarse.Edge,
      ∃ oriented ∈ refinement.combinatorial.edgeWord coarseEdge,
        OrientedEdge.underlying oriented = edge) ∨ edge ∈ tree

namespace TwoDimensionalDriverAxialEnlargementData

/-- Exact restriction from enlarged edge coordinates to coarse path holonomies. -/
def coarseRestriction
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)) :
    (enlarged.Edge → G) → (coarse.Edge → G) :=
  data.refinement.combinatorial.configurationMap

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] in
/-- Coarse restriction is measurable. -/
theorem coarseRestriction_measurable
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)) :
    Measurable data.coarseRestriction :=
  data.refinement.configurationMap_measurable

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- On every ambient connection, exact enlarged-path restriction recovers the original coarse
holonomies. -/
theorem ambient_coarseRestriction
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (connection : Connection) :
    data.coarseRestriction
        (fun edge => base.holonomy (enlarged.edgePath edge) connection) =
      fun edge => base.holonomy (coarse.edgePath edge) connection :=
  data.refinement.ambientConfiguration_compatibility connection

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- No enlarged edge is disconnected from both the original coarse paths and Driver's added tree. -/
theorem enlargedEdge_covered
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (edge : enlarged.Edge) :
    (∃ coarseEdge : coarse.Edge,
      ∃ oriented ∈ data.refinement.combinatorial.edgeWord coarseEdge,
        OrientedEdge.underlying oriented = edge) ∨ edge ∈ data.tree :=
  data.enlargedEdge_coarseSubdivision_or_tree edge

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The distinguished tree has exactly Driver's vertical/x-axis scope. -/
theorem tree_exact
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (edge : enlarged.Edge) :
    edge ∈ data.tree ↔
      TwoDimensionalEmbeddedEdgeIsVertical edge ∨
        TwoDimensionalEmbeddedEdgeIsOnXAxis edge :=
  data.tree_mem_iff_vertical_or_xAxis edge

end TwoDimensionalDriverAxialEnlargementData

end

end YangMills.Dimensions
