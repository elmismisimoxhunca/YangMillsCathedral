/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAxialEnlargement

/-!
# Probes for Driver's axial enlargement
-/

namespace YangMills.Dimensions.TwoDimensionalDriverAxialEnlargement.Probes

open MeasureTheory
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
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    {enlarged : TwoDimensionalEmbeddedPlanarGraphData.{uLargeVertex, uLargeEdge,
      uLargeFace, uLargeXAxisCell} base}
    [DecidableEq coarse.Edge] [DecidableEq enlarged.Edge]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The enlargement simultaneously carries BC geometry, exact refinement, and Driver's tree. -/
theorem exact_enlargement_contract
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)) :
    (∀ face, IsConnected (frontier (coarse.faceRegion face))) ∧
      (∀ face, IsConnected (frontier (enlarged.faceRegion face))) ∧
      FiniteGraphEdgeSetIsTree enlarged.edgeSource enlarged.edgeTarget data.tree ∧
      (∀ edge, edge ∈ data.tree ↔
        TwoDimensionalEmbeddedEdgeIsVertical edge ∨
          TwoDimensionalEmbeddedEdgeIsOnXAxis edge) :=
  ⟨data.coarseBoundaryConnected.face_frontier_connected,
    data.enlargedBoundaryConnected.face_frontier_connected,
    data.tree_is_driver, data.tree_exact⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] in
/-- Exact enlarged configurations restrict measurably to coarse path holonomies. -/
theorem exact_restriction_measurable
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged)) :
    Measurable data.coarseRestriction :=
  data.coarseRestriction_measurable

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- On every ambient connection, enlarged restriction is literally the original coarse holonomy. -/
theorem exact_ambient_restriction
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (connection : Connection) :
    data.coarseRestriction
        (fun edge => base.holonomy (enlarged.edgePath edge) connection) =
      fun edge => base.holonomy (coarse.edgePath edge) connection :=
  data.ambient_coarseRestriction connection

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Actual complex coarse observables agree on continuum holonomies before and after restriction. -/
theorem exact_ambient_observable_factorization
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (observable : (coarse.Edge → G) → ℂ)
    (connection : Connection) :
    observable (data.coarseRestriction
      (fun edge => base.holonomy (enlarged.edgePath edge) connection)) =
      observable (fun edge => base.holonomy (coarse.edgePath edge) connection) := by
  rw [data.ambient_coarseRestriction connection]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- An enlarged edge disconnected from both coarse subdivisions and the tree is rejected. -/
theorem unrelated_enlarged_edge_blocked
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (edge : enlarged.Edge)
    (notCoarse : ¬ ∃ coarseEdge : coarse.Edge,
      ∃ oriented ∈ data.refinement.combinatorial.edgeWord coarseEdge,
        OrientedEdge.underlying oriented = edge)
    (notTree : edge ∉ data.tree) : False := by
  rcases data.enlargedEdge_covered edge with coarseUse | treeUse
  · exact notCoarse coarseUse
  · exact notTree treeUse

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- A tree edge that is neither vertical nor on the x-axis is hostilely rejected. -/
theorem wrong_tree_edge_blocked
    (data : TwoDimensionalDriverAxialEnlargementData
      (G := G) (coarse := coarse) (enlarged := enlarged))
    (edge : enlarged.Edge) (membership : edge ∈ data.tree)
    (notVertical : ¬ TwoDimensionalEmbeddedEdgeIsVertical edge)
    (notXAxis : ¬ TwoDimensionalEmbeddedEdgeIsOnXAxis edge) : False := by
  rcases (data.tree_exact edge).mp membership with vertical | xAxis
  · exact notVertical vertical
  · exact notXAxis xAxis

end

end YangMills.Dimensions.TwoDimensionalDriverAxialEnlargement.Probes
