/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGaugeFixedHolonomyMeasure
import YangMills.Mathematics.FiniteOrientedEdgeGaugeTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exact simple-boundary planar graph data in dimension two

Driver's Definition 6.2 and Theorem 6.6 require an actual finite directed planar graph, not merely a
free finite face label. This module introduces a concrete acceptance certificate tied to the exact
ambient path carrier. Every path receives a continuous coordinate realization in `ℝ²`; graph edges
select exact ambient paths, are injective on `[0,1]`, and may intersect distinct edges only at shared
endpoint points. The complement of the total trace is required to be exactly one unbounded region
plus the supplied bounded connected open face regions. Every face frontier has a once-around Jordan parameterization realized segment-by-segment by one
nonempty closed composable oriented boundary word with no repeated underlying edge, and its supplied
positive real area is tied to coordinate Lebesgue volume. This deliberately treats a simple-boundary
subclass: general BC boundaries with bridge multiplicity remain later work. Driver's piecewise-`C¹`
vertical/horizontal admissibility is also still a separate strengthening; continuity alone is not
presented as that source hypothesis.

This is uninhabited topological geometric acceptance data. It constructs no graph, face, measure, density, or
Yang--Mills object. It covers only simple-boundary face presentations. Driver's general
multiple-boundary-component/cut-choice theorem requires a separate interface.
-/

namespace YangMills.Dimensions

open Set MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uG uGauge uSample uConnection uVertex uEdge uFace

/-- Coordinate Lebesgue volume of a set in literal two-dimensional Euclidean spacetime. The set
is sent through Mathlib's canonical Euclidean-space coordinate equivalence and measured by the
finite product of standard real Lebesgue measures. This avoids installing a competing global
measurable-space instance on `EuclideanSpace`. -/
noncomputable def twoDimensionalCoordinateLebesgueVolume
    (region : Set EuclideanDimension.two.Spacetime) : ENNReal :=
  (Measure.pi (fun _ : EuclideanDimension.two.CoordinateIndex => MeasureTheory.volume))
    ((EuclideanSpace.equiv EuclideanDimension.two.CoordinateIndex ℝ) '' region)

/-- Coordinate trace of one exact selected ambient edge path over the closed unit interval. -/
def finiteEmbeddedEdgeTrace
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {Edge : Type uEdge}
    (pathCurve : base.Path → ℝ → EuclideanDimension.two.Spacetime)
    (edgePath : Edge → base.Path) (edge : Edge) :
    Set EuclideanDimension.two.Spacetime :=
  pathCurve (edgePath edge) '' Set.Icc 0 1

/-- Union of all traces in the exact finite edge index. -/
def finiteEmbeddedGraphTrace
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (Edge : Type uEdge)
    (pathCurve : base.Path → ℝ → EuclideanDimension.two.Spacetime)
    (edgePath : Edge → base.Path) : Set EuclideanDimension.two.Spacetime :=
  ⋃ edge : Edge, finiteEmbeddedEdgeTrace pathCurve edgePath edge

/-- Unoriented trace union named by one finite oriented boundary word. -/
def finiteBoundaryWordTrace
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {Edge : Type uEdge}
    (pathCurve : base.Path → ℝ → EuclideanDimension.two.Spacetime)
    (edgePath : Edge → base.Path) (word : List (OrientedEdge Edge)) :
    Set EuclideanDimension.two.Spacetime :=
  ⋃ oriented ∈ word,
    finiteEmbeddedEdgeTrace pathCurve edgePath (OrientedEdge.underlying oriented)

/-- Coordinate curve for one oriented selected edge. Reverse orientation uses the same underlying
ambient path curve with parameter `t ↦ 1 - t`. -/
def finiteOrientedEdgeCurve
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {Edge : Type uEdge}
    (pathCurve : base.Path → ℝ → EuclideanDimension.two.Spacetime)
    (edgePath : Edge → base.Path) : OrientedEdge Edge → ℝ → EuclideanDimension.two.Spacetime
  | .forward edge => pathCurve (edgePath edge)
  | .reverse edge => fun t => pathCurve (edgePath edge) (1 - t)

/-- Concrete topological certificate for a finite directed planar graph whose bounded faces all
have one simple once-around boundary component. This is a source-facing strengthening to the
Jordan-boundary subclass of Driver's BC graphs. The face index may be empty, retaining legitimate
planar trees and empty graphs. -/
structure TwoDimensionalSimpleBoundaryPlanarGraphData
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    (base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection) where
  /-- Finite vertices, underlying edge coordinates, and bounded complementary faces. -/
  Vertex : Type uVertex
  Edge : Type uEdge
  Face : Type uFace
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  faceFintype : Fintype Face
  /-- Literal separated vertex locations in two-dimensional Euclidean spacetime. -/
  vertexPoint : Vertex → EuclideanDimension.two.Spacetime
  vertexPoint_injective : Function.Injective vertexPoint
  /-- Coordinate realization of every exact ambient path, coherent with reversal and concatenation.
  Source-specific piecewise-`C¹` admissibility remains an additional later strengthening. -/
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
  /-- Positive underlying edges select exact ambient paths and exact combinatorial endpoints. -/
  edgePath : Edge → base.Path
  edgeSource : Edge → Vertex
  edgeTarget : Edge → Vertex
  edgePath_source : ∀ edge,
    base.pathSource (edgePath edge) = vertexPoint (edgeSource edge)
  edgePath_target : ∀ edge,
    base.pathTarget (edgePath edge) = vertexPoint (edgeTarget edge)
  /-- No isolated combinatorial vertex is hidden outside the embedded trace. -/
  vertex_incident : ∀ vertex, ∃ edge,
    edgeSource edge = vertex ∨ edgeTarget edge = vertex
  /-- Every edge is an embedded arc on `[0,1]`. This excludes one-edge loops; Driver graphs with
  loop incidence must first be subdivided. -/
  edgeCurve_injective : ∀ edge,
    Set.InjOn (pathCurve (edgePath edge)) (Set.Icc 0 1)
  /-- Distinct arcs intersect only at endpoint points shared by both edges. -/
  distinct_edge_intersection : ∀ first second, first ≠ second →
    finiteEmbeddedEdgeTrace pathCurve edgePath first ∩
        finiteEmbeddedEdgeTrace pathCurve edgePath second ⊆
      ({vertexPoint (edgeSource first), vertexPoint (edgeTarget first)} :
          Set EuclideanDimension.two.Spacetime) ∩
        ({vertexPoint (edgeSource second), vertexPoint (edgeTarget second)} :
          Set EuclideanDimension.two.Spacetime)
  /-- One exact nonempty connected boundary word per bounded face. -/
  boundaryWord : Face → List (OrientedEdge Edge)
  boundaryWord_nonempty : ∀ face, boundaryWord face ≠ []
  /-- The simple-boundary subclass uses every underlying edge at most once on one face frontier,
  ruling out doubled circuits. General BC graphs with bridge multiplicity remain separate debt. -/
  boundaryWord_underlying_nodup : ∀ face,
    ((boundaryWord face).map OrientedEdge.underlying).Nodup
  boundaryWord_chain : ∀ face,
    List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) (boundaryWord face)
  boundaryWord_closed : ∀ face,
    OrientedEdge.target edgeSource edgeTarget
        ((boundaryWord face).getLast (boundaryWord_nonempty face)) =
      OrientedEdge.source edgeSource edgeTarget
        ((boundaryWord face).head (boundaryWord_nonempty face))
  /-- A once-around Jordan parameterization ties word order, not merely its trace set, to the exact
  face frontier. -/
  boundaryTraversal : Face → ℝ → EuclideanDimension.two.Spacetime
  boundaryTraversal_continuousOn : ∀ face,
    ContinuousOn (boundaryTraversal face) (Set.Icc 0 1)
  boundaryTraversal_closed : ∀ face,
    boundaryTraversal face 0 = boundaryTraversal face 1
  boundaryTraversal_injectiveOn : ∀ face,
    Set.InjOn (boundaryTraversal face) (Set.Ico 0 1)
  boundaryWord_realizes_traversal : ∀ face
      (index : Fin (boundaryWord face).length) (t : ℝ), t ∈ Set.Icc 0 1 →
    boundaryTraversal face
        (((index.1 : ℝ) + t) / ((boundaryWord face).length : ℝ)) =
      finiteOrientedEdgeCurve pathCurve edgePath ((boundaryWord face).get index) t
  /-- Exact bounded complementary regions and the one unbounded complementary region. -/
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
  /-- The supplied regions are exactly all connected complementary pieces. -/
  complement_decomposition :
    (finiteEmbeddedGraphTrace Edge pathCurve edgePath)ᶜ =
      unboundedRegion ∪ ⋃ face : Face, faceRegion face
  /-- Boundary-connectedness and exact edge incidence for each face. -/
  face_frontier : ∀ face,
    frontier (faceRegion face) =
      finiteBoundaryWordTrace pathCurve edgePath (boundaryWord face)
  boundaryTraversal_range : ∀ face,
    boundaryTraversal face '' Set.Icc 0 1 = frontier (faceRegion face)
  /-- Positive area is the actual coordinate Lebesgue volume of the exact face region. -/
  faceArea : Face → ℝ
  faceArea_pos : ∀ face, 0 < faceArea face
  faceArea_eq_volume : ∀ face,
    twoDimensionalCoordinateLebesgueVolume (faceRegion face) =
      ENNReal.ofReal (faceArea face)

attribute [instance]
  TwoDimensionalSimpleBoundaryPlanarGraphData.vertexFintype
  TwoDimensionalSimpleBoundaryPlanarGraphData.edgeFintype
  TwoDimensionalSimpleBoundaryPlanarGraphData.faceFintype

end

end YangMills.Dimensions
