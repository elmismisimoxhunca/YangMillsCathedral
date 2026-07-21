/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalEmbeddedPlanarGraph

/-!
# Probes for the boundary-neutral embedded planar graph

The probes pin exact preservation under forgetting a simple boundary presentation and expose the
complement, x-axis, admissibility, and area obligations independently of any boundary word.
-/

namespace YangMills.Dimensions.TwoDimensionalEmbeddedPlanarGraph.Probes

open Set MeasureTheory

noncomputable section

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}

/-- Forgetting a simple boundary presentation retains the identical selected ambient edge path. -/
theorem exact_edge_path_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) (edge : graph.Edge) :
    graph.toEmbeddedPlanarGraphData.edgePath edge = graph.edgePath edge :=
  rfl

/-- Every stored edge remains an embedded arc on `[0,1]`; one-edge loops require subdivision. -/
theorem exact_embedded_arc_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) (edge : graph.Edge) :
    Set.InjOn (graph.pathCurve (graph.edgePath edge)) (Set.Icc 0 1) :=
  graph.toEmbeddedPlanarGraphData.edgeCurve_injective edge

/-- Distinct embedded arcs can meet only at endpoint points shared by both edges. -/
theorem exact_endpoint_only_intersection_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base)
    (first second : graph.Edge) (different : first ≠ second) :
    finiteEmbeddedEdgeTrace graph.pathCurve graph.edgePath first ∩
        finiteEmbeddedEdgeTrace graph.pathCurve graph.edgePath second ⊆
      ({graph.vertexPoint (graph.edgeSource first), graph.vertexPoint (graph.edgeTarget first)} :
          Set EuclideanDimension.two.Spacetime) ∩
        ({graph.vertexPoint (graph.edgeSource second), graph.vertexPoint (graph.edgeTarget second)} :
          Set EuclideanDimension.two.Spacetime) :=
  graph.toEmbeddedPlanarGraphData.distinct_edge_intersection first second different

/-- A proposed non-endpoint crossing of distinct stored arcs is rejected. -/
theorem nonendpoint_crossing_blocked
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base)
    (first second : graph.Edge) (different : first ≠ second)
    (point : EuclideanDimension.two.Spacetime)
    (in_both : point ∈ finiteEmbeddedEdgeTrace graph.pathCurve graph.edgePath first ∩
      finiteEmbeddedEdgeTrace graph.pathCurve graph.edgePath second)
    (not_shared_endpoints : point ∉
      ({graph.vertexPoint (graph.edgeSource first), graph.vertexPoint (graph.edgeTarget first)} :
          Set EuclideanDimension.two.Spacetime) ∩
        ({graph.vertexPoint (graph.edgeSource second), graph.vertexPoint (graph.edgeTarget second)} :
          Set EuclideanDimension.two.Spacetime)) : False :=
  not_shared_endpoints
    (graph.toEmbeddedPlanarGraphData.distinct_edge_intersection first second different in_both)

/-- Exact complement components are retained, not replaced by freely labeled faces. -/
theorem exact_complement_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) :
    (finiteEmbeddedGraphTrace graph.Edge graph.pathCurve graph.edgePath)ᶜ =
      graph.unboundedRegion ∪ ⋃ face : graph.Face, graph.faceRegion face :=
  graph.toEmbeddedPlanarGraphData.complement_decomposition

/-- Distinct bounded complementary regions remain pairwise disjoint. -/
theorem exact_face_separation_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base)
    (first second : graph.Face) (different : first ≠ second) :
    Disjoint (graph.faceRegion first) (graph.faceRegion second) :=
  graph.toEmbeddedPlanarGraphData.faceRegion_disjoint first second different

/-- The unbounded component remains disjoint from every bounded face component. -/
theorem exact_unbounded_face_separation_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) (face : graph.Face) :
    Disjoint graph.unboundedRegion (graph.faceRegion face) :=
  graph.toEmbeddedPlanarGraphData.unboundedRegion_disjoint_face face

/-- Driver's augmented x-axis finite-cell decomposition remains part of boundary-neutral geometry. -/
theorem exact_xAxis_decomposition_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) :
    (finiteEmbeddedGraphTrace graph.Edge graph.pathCurve graph.edgePath ∪
        twoDimensionalXAxis)ᶜ =
      ⋃ cell : graph.XAxisCell, graph.xAxisCellRegion cell :=
  graph.toEmbeddedPlanarGraphData.xAxisComplement_decomposition

/-- Exact Driver admissibility remains attached to each unchanged selected ambient edge path. -/
theorem exact_edge_admissibility_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) (edge : graph.Edge) :
    Nonempty (DriverAdmissibleCurveCertificate (graph.pathCurve (graph.edgePath edge))) :=
  ⟨graph.toEmbeddedPlanarGraphData.edgePath_admissible edge⟩

/-- Exact coordinate-Lebesgue area survives forgetting boundary words and traversal choices. -/
theorem exact_face_area_preserved
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) (face : graph.Face) :
    twoDimensionalCoordinateLebesgueVolume (graph.faceRegion face) =
      ENNReal.ofReal (graph.faceArea face) :=
  graph.toEmbeddedPlanarGraphData.faceArea_eq_volume face

/-- A substituted edge path is rejected whenever it differs from the retained selected path. -/
theorem substituted_edge_path_blocked
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) (edge : graph.Edge)
    (wrong : base.Path) (different : wrong ≠ graph.edgePath edge)
    (claimed : graph.toEmbeddedPlanarGraphData.edgePath edge = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

/-- Boundary-neutral geometry is still intrinsically two-dimensional. -/
theorem embedded_planar_graph_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalEmbeddedPlanarGraph.Probes
