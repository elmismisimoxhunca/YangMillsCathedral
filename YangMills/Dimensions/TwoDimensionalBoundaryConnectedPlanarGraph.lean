/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalEmbeddedPlanarGraph
import YangMills.Mathematics.FiniteBoundaryConnectedWord

/-!
# Embedded boundary-connected planar graphs in dimension two

Driver calls a planar graph BC when every bounded complementary region has connected boundary. This
module combines the project's conservative embedded-arc strengthening of the exact boundary-neutral
geometry with that literal frontier condition and an
ordered closed boundary traversal. Unlike the earlier Jordan subclass, the traversal need not be
injective: an actual graph-theoretic bridge may occur once in each opposite orientation. Nonbridge
edges remain at-most-once, so doubling an ordinary boundary circuit is still rejected.

Driver-permitted one-edge loop incidence must be subdivided before entering this strengthened
embedded-arc subclass. This is uninhabited topological/combinatorial acceptance data. It constructs no graph instance,
density, face law, probability measure, or Yang--Mills theory. Driver's general non-BC cut choices
and their integral-level independence remain a separate interface.
-/

namespace YangMills.Dimensions

open Set
open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uFace uXAxisCell

/-- Exact embedded BC planar graph data with bridge-aware ordered boundary traversals. -/
structure TwoDimensionalBoundaryConnectedPlanarGraphData
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    (base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base)
    [DecidableEq embedded.Edge] where
  boundaryWord : embedded.Face → List (OrientedEdge embedded.Edge)
  /-- Closed/composable words with exact graph-theoretic bridge multiplicities. -/
  boundaryWord_certificate : ∀ face,
    BoundaryConnectedWordCertificate embedded.edgeSource embedded.edgeTarget (boundaryWord face)
  /-- Ordered piecewise edge traversal. It may retrace an actual bridge but no nonbridge circuit. -/
  boundaryTraversal : embedded.Face → ℝ → EuclideanDimension.two.Spacetime
  boundaryTraversal_continuousOn : ∀ face,
    ContinuousOn (boundaryTraversal face) (Set.Icc 0 1)
  boundaryTraversal_closed : ∀ face,
    boundaryTraversal face 0 = boundaryTraversal face 1
  boundaryWord_realizes_traversal : ∀ face
      (index : Fin (boundaryWord face).length) (t : ℝ), t ∈ Set.Icc 0 1 →
    boundaryTraversal face
        (((index.1 : ℝ) + t) / ((boundaryWord face).length : ℝ)) =
      finiteOrientedEdgeCurve embedded.pathCurve embedded.edgePath
        ((boundaryWord face).get index) t
  /-- Literal BC condition on the exact topological frontier. -/
  face_frontier_connected : ∀ face,
    IsConnected (frontier (embedded.faceRegion face))
  /-- The exact word uses exactly the edges in that frontier, including legitimate bridge repeats. -/
  face_frontier : ∀ face,
    frontier (embedded.faceRegion face) =
      finiteBoundaryWordTrace embedded.pathCurve embedded.edgePath (boundaryWord face)
  /-- The ordered traversal covers the whole exact frontier. -/
  boundaryTraversal_range : ∀ face,
    boundaryTraversal face '' Set.Icc 0 1 = frontier (embedded.faceRegion face)

namespace TwoDimensionalBoundaryConnectedPlanarGraphData

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {embedded : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq embedded.Edge]
    (graph : TwoDimensionalBoundaryConnectedPlanarGraphData base embedded)

/-- Every BC boundary word is nonempty. -/
theorem boundaryWord_nonempty (face : embedded.Face) :
    graph.boundaryWord face ≠ [] :=
  (graph.boundaryWord_certificate face).nonempty

/-- Every repeated underlying boundary edge is an actual graph-theoretic bridge. -/
theorem repeated_boundary_edge_is_bridge
    (face : embedded.Face) (edge : embedded.Edge)
    (repeated : 2 ≤
      (graph.boundaryWord face).count (.forward edge) +
        (graph.boundaryWord face).count (.reverse edge)) :
    FiniteGraphEdgeIsBridge embedded.edgeSource embedded.edgeTarget edge :=
  (graph.boundaryWord_certificate face).repeated_underlying_edge_is_bridge edge repeated

/-- Every nonbridge edge occurs at most once total on one exact face boundary. -/
theorem nonbridge_boundary_count_le_one
    (face : embedded.Face) (edge : embedded.Edge)
    (not_bridge :
      ¬ FiniteGraphEdgeIsBridge embedded.edgeSource embedded.edgeTarget edge) :
    (graph.boundaryWord face).count (.forward edge) +
        (graph.boundaryWord face).count (.reverse edge) ≤ 1 :=
  (graph.boundaryWord_certificate face).nonbridge_total_count_le_one edge not_bridge

end TwoDimensionalBoundaryConnectedPlanarGraphData

end

end YangMills.Dimensions
