/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalBoundaryConnectedPlanarGraph

/-!
# Probes for embedded boundary-connected planar graphs

The probes pin the literal connected-frontier condition, exact ordered edge realization, legitimate
bridge multiplicity, doubled-cycle rejection, unchanged embedded geometry, and dimensional scope.
-/

namespace YangMills.Dimensions.TwoDimensionalBoundaryConnectedPlanarGraph.Probes

open Set
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq embedded.Edge]
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded)

/-- BC means literal connectedness of each exact bounded-component frontier. -/
theorem exact_connected_frontier
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded)
    (face : embedded.Face) :
    IsConnected (frontier (embedded.faceRegion face)) :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.face_frontier_connected graph face

/-- The exact frontier is the trace of the supplied ordered bridge-aware word. -/
theorem exact_boundary_trace (face : embedded.Face) :
    frontier (embedded.faceRegion face) =
      finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face) :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.face_frontier graph face

/-- Every boundary word remains nonempty and closed/composable through its exact certificate. -/
theorem exact_nonempty_boundary (face : embedded.Face) :
    TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face ≠ [] :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord_nonempty graph face

/-- Every adjacent pair in the exact boundary word is endpoint-composable. -/
theorem exact_boundary_chain (face : embedded.Face) :
    List.IsChain (OrientedEdgeComposable embedded.edgeSource embedded.edgeTarget)
      (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face) :=
  (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord_certificate graph face).chain

/-- The terminal and initial vertices of every exact boundary word agree. -/
theorem exact_closed_boundary (face : embedded.Face) :
    let certificate :=
      TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord_certificate graph face
    let word := TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face
    OrientedEdge.target embedded.edgeSource embedded.edgeTarget
        (word.getLast certificate.nonempty) =
      OrientedEdge.source embedded.edgeSource embedded.edgeTarget
        (word.head certificate.nonempty) :=
  (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord_certificate graph face).closed

/-- The supplied ordered boundary traversal is continuous on the exact unit interval. -/
theorem exact_boundary_traversal_continuous (face : embedded.Face) :
    ContinuousOn
      (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal graph face)
      (Set.Icc 0 1) :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal_continuousOn graph face

/-- The supplied ordered boundary traversal is a closed circuit. -/
theorem exact_boundary_traversal_closed (face : embedded.Face) :
    TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal graph face 0 =
      TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal graph face 1 :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal_closed graph face

/-- A legitimate bridge has equal opposite-orientation multiplicity, each at most one. -/
theorem exact_bridge_multiplicity (face : embedded.Face) (edge : embedded.Edge)
    (bridge : FiniteGraphEdgeIsBridge embedded.edgeSource embedded.edgeTarget edge) :
    (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.forward edge) =
        (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.reverse edge) ∧
      (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.forward edge) ≤ 1 ∧
      (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.reverse edge) ≤ 1 := by
  have certificate := TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord_certificate graph face
  exact ⟨certificate.bridge_forward_count_eq_reverse_count edge bridge,
    certificate.bridge_forward_le_one edge bridge,
    certificate.bridge_reverse_count_le_one edge bridge⟩

/-- Doubling an edge lying on a cycle is rejected even though actual bridges may repeat. -/
theorem doubled_cycle_boundary_blocked
    (face : embedded.Face) (edge : embedded.Edge)
    (alternative : ∃ path : List (OrientedEdge embedded.Edge),
      OrientedEdgeWordRunsFrom embedded.edgeSource embedded.edgeTarget path
        (embedded.edgeSource edge) (embedded.edgeTarget edge) ∧
      ∀ oriented ∈ path, OrientedEdge.underlying oriented ≠ edge)
    (repeated : 2 ≤
      (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.forward edge) +
        (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.reverse edge)) : False := by
  have bridge := TwoDimensionalBoundaryConnectedPlanarGraphData.repeated_boundary_edge_is_bridge graph face edge repeated
  exact bridge alternative

/-- Nonbridge boundary edges occur at most once in both orientations combined. -/
theorem exact_nonbridge_count
    (face : embedded.Face) (edge : embedded.Edge)
    (not_bridge : ¬ FiniteGraphEdgeIsBridge embedded.edgeSource embedded.edgeTarget edge) :
    (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.forward edge) +
        (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).count (.reverse edge) ≤ 1 :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.nonbridge_boundary_count_le_one graph face edge not_bridge

/-- Word order is tied segment-by-segment to the exact oriented ambient edge curve. -/
theorem exact_ordered_segment
    (face : embedded.Face) (index : Fin (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).length)
    (t : ℝ) (in_unit : t ∈ Set.Icc (0 : ℝ) 1) :
    TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal graph face
        (((index.1 : ℝ) + t) / ((TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).length : ℝ)) =
      finiteOrientedEdgeCurve embedded.pathCurve embedded.edgePath
        ((TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face).get index) t :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord_realizes_traversal graph face index t in_unit

/-- The ordered traversal covers the whole exact frontier. -/
theorem exact_boundary_range (face : embedded.Face) :
    TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal graph face '' Set.Icc 0 1 = frontier (embedded.faceRegion face) :=
  TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryTraversal_range graph face

/-- A substituted frontier is rejected whenever it differs from the exact complementary face. -/
theorem substituted_frontier_blocked
    (face : embedded.Face) (wrong : Set EuclideanDimension.two.Spacetime)
    (different : wrong ≠ finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath
      (TwoDimensionalBoundaryConnectedPlanarGraphData.boundaryWord graph face))
    (claimed : frontier (embedded.faceRegion face) = wrong) : False := by
  apply different
  rw [← claimed]
  exact TwoDimensionalBoundaryConnectedPlanarGraphData.face_frontier graph face

/-- The embedded BC interface remains strictly two-dimensional evidence. -/
theorem boundary_connected_planar_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalBoundaryConnectedPlanarGraph.Probes
