/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSimpleBoundaryPlanarGraph

/-!
# Embedded finite planar graph skeleton in dimension two

This module factors the boundary-neutral geometry shared by the Jordan/simple-boundary, the project's strengthened embedded-arc
boundary-connected, and later disconnected-boundary interfaces. It retains exact ambient paths,
Driver admissibility, embedded arcs, complement components, the x-axis finite-cell condition, and
geometric face areas, but intentionally supplies no boundary words or boundary traversal choices.

The record is uninhabited acceptance data. It constructs no planar graph instance, density,
probability measure, holonomy law, or Yang--Mills theory.
-/

namespace YangMills.Dimensions

open Set MeasureTheory

noncomputable section

universe uVertex uEdge uFace uXAxisCell

/-- Boundary-neutral embedded planar graph geometry shared by later boundary presentations. -/
structure TwoDimensionalEmbeddedPlanarGraphData
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    (base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection) where
  Vertex : Type uVertex
  Edge : Type uEdge
  Face : Type uFace
  XAxisCell : Type uXAxisCell
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  faceFintype : Fintype Face
  xAxisCellFintype : Fintype XAxisCell
  vertexPoint : Vertex → EuclideanDimension.two.Spacetime
  vertexPoint_injective : Function.Injective vertexPoint
  /-- Exact coordinate realization of every ambient path, preserving path operations. -/
  pathCurve : base.Path → ℝ → EuclideanDimension.two.Spacetime
  pathCurve_continuous : ∀ path, Continuous (pathCurve path)
  pathCurve_source : ∀ path, pathCurve path 0 = base.pathSource path
  pathCurve_target : ∀ path, pathCurve path 1 = base.pathTarget path
  pathCurve_reverse : ∀ path t, t ∈ Set.Icc (0 : ℝ) 1 →
    pathCurve (base.reverse path) t = pathCurve path (1 - t)
  pathCurve_concat : ∀ first second, base.composable first second → ∀ t,
    t ∈ Set.Icc (0 : ℝ) 1 →
      pathCurve (base.concat first second) t =
        if t ≤ 1 / 2 then pathCurve first (2 * t)
        else pathCurve second (2 * t - 1)
  edgePath : Edge → base.Path
  edgeSource : Edge → Vertex
  edgeTarget : Edge → Vertex
  edgePath_source : ∀ edge,
    base.pathSource (edgePath edge) = vertexPoint (edgeSource edge)
  edgePath_target : ∀ edge,
    base.pathTarget (edgePath edge) = vertexPoint (edgeTarget edge)
  edgePath_admissible : ∀ edge,
    DriverAdmissibleCurveCertificate (pathCurve (edgePath edge))
  vertex_incident : ∀ vertex, ∃ edge,
    edgeSource edge = vertex ∨ edgeTarget edge = vertex
  /-- Every stored edge is an embedded arc. This conservative strengthening excludes a one-edge
  loop; Driver-permitted endpoint self-incidence must first be subdivided into embedded arcs. -/
  edgeCurve_injective : ∀ edge,
    Set.InjOn (pathCurve (edgePath edge)) (Set.Icc 0 1)
  distinct_edge_intersection : ∀ first second, first ≠ second →
    finiteEmbeddedEdgeTrace pathCurve edgePath first ∩
        finiteEmbeddedEdgeTrace pathCurve edgePath second ⊆
      ({vertexPoint (edgeSource first), vertexPoint (edgeTarget first)} :
          Set EuclideanDimension.two.Spacetime) ∩
        ({vertexPoint (edgeSource second), vertexPoint (edgeTarget second)} :
          Set EuclideanDimension.two.Spacetime)
  /-- Exact bounded and unbounded connected components of the graph-trace complement. -/
  faceRegion : Face → Set EuclideanDimension.two.Spacetime
  unboundedRegion : Set EuclideanDimension.two.Spacetime
  faceRegion_nonempty : ∀ face, (faceRegion face).Nonempty
  faceRegion_open : ∀ face, IsOpen (faceRegion face)
  faceRegion_connected : ∀ face, IsConnected (faceRegion face)
  faceRegion_bounded : ∀ face, Bornology.IsBounded (faceRegion face)
  faceRegion_disjoint : ∀ first second, first ≠ second →
    Disjoint (faceRegion first) (faceRegion second)
  unboundedRegion_disjoint_face : ∀ face,
    Disjoint unboundedRegion (faceRegion face)
  unboundedRegion_nonempty : unboundedRegion.Nonempty
  unboundedRegion_open : IsOpen unboundedRegion
  unboundedRegion_connected : IsConnected unboundedRegion
  unboundedRegion_not_bounded : ¬ Bornology.IsBounded unboundedRegion
  complement_decomposition :
    (finiteEmbeddedGraphTrace Edge pathCurve edgePath)ᶜ =
      unboundedRegion ∪ ⋃ face : Face, faceRegion face
  /-- Exact finite connected-cell decomposition after adjoining Driver's x-axis. -/
  xAxisCellRegion : XAxisCell → Set EuclideanDimension.two.Spacetime
  xAxisCellRegion_nonempty : ∀ cell, (xAxisCellRegion cell).Nonempty
  xAxisCellRegion_open : ∀ cell, IsOpen (xAxisCellRegion cell)
  xAxisCellRegion_connected : ∀ cell, IsConnected (xAxisCellRegion cell)
  xAxisCellRegion_disjoint : ∀ first second, first ≠ second →
    Disjoint (xAxisCellRegion first) (xAxisCellRegion second)
  xAxisComplement_decomposition :
    (finiteEmbeddedGraphTrace Edge pathCurve edgePath ∪ twoDimensionalXAxis)ᶜ =
      ⋃ cell : XAxisCell, xAxisCellRegion cell
  xAxisCell_frontier : ∀ cell,
    frontier (xAxisCellRegion cell) ⊆
      finiteEmbeddedGraphTrace Edge pathCurve edgePath ∪ twoDimensionalXAxis
  /-- Exact positive coordinate-Lebesgue area of every bounded complementary component. -/
  faceArea : Face → ℝ
  faceArea_pos : ∀ face, 0 < faceArea face
  faceArea_eq_volume : ∀ face,
    twoDimensionalCoordinateLebesgueVolume (faceRegion face) =
      ENNReal.ofReal (faceArea face)

attribute [instance]
  TwoDimensionalEmbeddedPlanarGraphData.vertexFintype
  TwoDimensionalEmbeddedPlanarGraphData.edgeFintype
  TwoDimensionalEmbeddedPlanarGraphData.faceFintype
  TwoDimensionalEmbeddedPlanarGraphData.xAxisCellFintype

namespace TwoDimensionalSimpleBoundaryPlanarGraphData

/-- Forget only the simple-boundary words/traversals while retaining the exact same embedded graph,
complement components, admissible ambient edge paths, x-axis cells, and geometric areas. -/
def toEmbeddedPlanarGraphData
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base) :
    TwoDimensionalEmbeddedPlanarGraphData base where
  Vertex := graph.Vertex
  Edge := graph.Edge
  Face := graph.Face
  XAxisCell := graph.XAxisCell
  vertexFintype := graph.vertexFintype
  edgeFintype := graph.edgeFintype
  faceFintype := graph.faceFintype
  xAxisCellFintype := graph.xAxisCellFintype
  vertexPoint := graph.vertexPoint
  vertexPoint_injective := graph.vertexPoint_injective
  pathCurve := graph.pathCurve
  pathCurve_continuous := graph.pathCurve_continuous
  pathCurve_source := graph.pathCurve_source
  pathCurve_target := graph.pathCurve_target
  pathCurve_reverse := graph.pathCurve_reverse
  pathCurve_concat := graph.pathCurve_concat
  edgePath := graph.edgePath
  edgeSource := graph.edgeSource
  edgeTarget := graph.edgeTarget
  edgePath_source := graph.edgePath_source
  edgePath_target := graph.edgePath_target
  edgePath_admissible := graph.edgePath_admissible
  vertex_incident := graph.vertex_incident
  edgeCurve_injective := graph.edgeCurve_injective
  distinct_edge_intersection := graph.distinct_edge_intersection
  faceRegion := graph.faceRegion
  unboundedRegion := graph.unboundedRegion
  faceRegion_nonempty := graph.faceRegion_nonempty
  faceRegion_open := graph.faceRegion_open
  faceRegion_connected := graph.faceRegion_connected
  faceRegion_bounded := graph.faceRegion_bounded
  faceRegion_disjoint := graph.faceRegion_disjoint
  unboundedRegion_disjoint_face := graph.unboundedRegion_disjoint_face
  unboundedRegion_nonempty := graph.unboundedRegion_nonempty
  unboundedRegion_open := graph.unboundedRegion_open
  unboundedRegion_connected := graph.unboundedRegion_connected
  unboundedRegion_not_bounded := graph.unboundedRegion_not_bounded
  complement_decomposition := graph.complement_decomposition
  xAxisCellRegion := graph.xAxisCellRegion
  xAxisCellRegion_nonempty := graph.xAxisCellRegion_nonempty
  xAxisCellRegion_open := graph.xAxisCellRegion_open
  xAxisCellRegion_connected := graph.xAxisCellRegion_connected
  xAxisCellRegion_disjoint := graph.xAxisCellRegion_disjoint
  xAxisComplement_decomposition := graph.xAxisComplement_decomposition
  xAxisCell_frontier := graph.xAxisCell_frontier
  faceArea := graph.faceArea
  faceArea_pos := graph.faceArea_pos
  faceArea_eq_volume := graph.faceArea_eq_volume

end TwoDimensionalSimpleBoundaryPlanarGraphData

end

end YangMills.Dimensions
