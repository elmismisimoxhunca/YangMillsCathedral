/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSimpleBoundaryPlanarGraph

/-!
# Probes for simple-boundary planar graph certificates

The probes retain exact ambient paths, embedded traces, complement decomposition, closed connected
boundary words, once-around traversal, and coordinate Lebesgue area. They reject doubled circuits
and replacing a face by a region with a different frontier, while retaining the legitimate
face-free case.
-/

namespace YangMills.Dimensions.TwoDimensionalSimpleBoundaryPlanarGraph.Probes

open Set
open YangMills.Mathematics

noncomputable section

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (graph : TwoDimensionalSimpleBoundaryPlanarGraphData base)

/-- Distinct combinatorial vertices have distinct literal coordinate locations. -/
theorem exact_vertex_separation : Function.Injective graph.vertexPoint :=
  graph.vertexPoint_injective

/-- Every selected edge remains the exact ambient path with literal vertex endpoints. -/
theorem exact_edge_path_endpoints (edge : graph.Edge) :
    base.pathSource (graph.edgePath edge) = graph.vertexPoint (graph.edgeSource edge) ∧
    base.pathTarget (graph.edgePath edge) = graph.vertexPoint (graph.edgeTarget edge) :=
  ⟨graph.edgePath_source edge, graph.edgePath_target edge⟩

/-- The path realization retains exact reversal on the closed parameter interval. -/
theorem exact_path_reverse (path : base.Path) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    graph.pathCurve (base.reverse path) t = graph.pathCurve path (1 - t) :=
  graph.pathCurve_reverse path t ht

/-- The path realization retains exact first-then-second concatenation geometry. -/
theorem exact_path_concat
    (first second : base.Path) (composable : base.composable first second)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    graph.pathCurve (base.concat first second) t =
      if t ≤ 1 / 2 then graph.pathCurve first (2 * t)
      else graph.pathCurve second (2 * t - 1) :=
  graph.pathCurve_concat first second composable t ht

/-- Embedded edges are injective and distinct edges cross only at shared endpoint coordinates. -/
theorem exact_embedded_edge_geometry
    (first second : graph.Edge) (different : first ≠ second) :
    Set.InjOn (graph.pathCurve (graph.edgePath first)) (Set.Icc 0 1) ∧
    finiteEmbeddedEdgeTrace graph.pathCurve graph.edgePath first ∩
        finiteEmbeddedEdgeTrace graph.pathCurve graph.edgePath second ⊆
      ({graph.vertexPoint (graph.edgeSource first),
          graph.vertexPoint (graph.edgeTarget first)} :
          Set EuclideanDimension.two.Spacetime) ∩
        ({graph.vertexPoint (graph.edgeSource second),
          graph.vertexPoint (graph.edgeTarget second)} :
          Set EuclideanDimension.two.Spacetime) :=
  ⟨graph.edgeCurve_injective first, graph.distinct_edge_intersection first second different⟩

/-- Every bounded face has one nonempty composable closed boundary word. -/
theorem exact_boundary_connected_cycle (face : graph.Face) :
    graph.boundaryWord face ≠ [] ∧
    List.IsChain (OrientedEdgeComposable graph.edgeSource graph.edgeTarget)
      (graph.boundaryWord face) ∧
    OrientedEdge.target graph.edgeSource graph.edgeTarget
        ((graph.boundaryWord face).getLast (graph.boundaryWord_nonempty face)) =
      OrientedEdge.source graph.edgeSource graph.edgeTarget
        ((graph.boundaryWord face).head (graph.boundaryWord_nonempty face)) :=
  ⟨graph.boundaryWord_nonempty face, graph.boundaryWord_chain face,
    graph.boundaryWord_closed face⟩

/-- The exact word has no repeated underlying edge and realizes a once-around Jordan traversal. -/
theorem exact_onceAround_boundary
    (face : graph.Face) :
    ((graph.boundaryWord face).map OrientedEdge.underlying).Nodup ∧
      Set.InjOn (graph.boundaryTraversal face) (Set.Ico 0 1) ∧
      graph.boundaryTraversal face '' Set.Icc 0 1 = frontier (graph.faceRegion face) :=
  ⟨graph.boundaryWord_underlying_nodup face,
    graph.boundaryTraversal_injectiveOn face, graph.boundaryTraversal_range face⟩

/-- Every ordered word segment is the exact corresponding oriented ambient edge curve. -/
theorem exact_boundary_segment_realization
    (face : graph.Face) (index : Fin (graph.boundaryWord face).length)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    graph.boundaryTraversal face
        (((index.1 : ℝ) + t) / ((graph.boundaryWord face).length : ℝ)) =
      finiteOrientedEdgeCurve graph.pathCurve graph.edgePath
        ((graph.boundaryWord face).get index) t :=
  graph.boundaryWord_realizes_traversal face index t ht

/-- A repeated full circuit cannot serve as the exact once-around boundary word. -/
theorem doubled_boundary_circuit_blocked
    (face : graph.Face) (word : List (OrientedEdge graph.Edge))
    (word_nonempty : word ≠ [])
    (claimed : graph.boundaryWord face = word ++ word) : False := by
  have nodup := graph.boundaryWord_underlying_nodup face
  rw [claimed, List.map_append, List.nodup_append] at nodup
  obtain ⟨oriented, member⟩ := List.exists_mem_of_ne_nil word word_nonempty
  have mapped_member : OrientedEdge.underlying oriented ∈ word.map OrientedEdge.underlying :=
    List.mem_map.mpr ⟨oriented, member, rfl⟩
  exact nodup.2.2 _ mapped_member _ mapped_member rfl

/-- The supplied pieces are exactly the complement of the actual finite embedded trace. -/
theorem exact_complement_decomposition :
    (finiteEmbeddedGraphTrace graph.Edge graph.pathCurve graph.edgePath)ᶜ =
      graph.unboundedRegion ∪ ⋃ face : graph.Face, graph.faceRegion face :=
  graph.complement_decomposition

/-- The unbounded component is disjoint from every exact bounded face. -/
theorem exact_unbounded_face_disjoint (face : graph.Face) :
    Disjoint graph.unboundedRegion (graph.faceRegion face) :=
  graph.unboundedRegion_disjoint_face face

/-- Distinct bounded face regions are exactly disjoint. -/
theorem exact_face_regions_disjoint
    (first second : graph.Face) (different : first ≠ second) :
    Disjoint (graph.faceRegion first) (graph.faceRegion second) :=
  graph.faceRegion_disjoint first second different

/-- Face frontier and positive area are tied to the same exact region and boundary word. -/
theorem exact_face_frontier_and_area (face : graph.Face) :
    frontier (graph.faceRegion face) =
        finiteBoundaryWordTrace graph.pathCurve graph.edgePath (graph.boundaryWord face) ∧
      0 < graph.faceArea face ∧
      twoDimensionalCoordinateLebesgueVolume (graph.faceRegion face) =
        ENNReal.ofReal (graph.faceArea face) :=
  ⟨graph.face_frontier face, graph.faceArea_pos face, graph.faceArea_eq_volume face⟩

/-- A region with a different frontier cannot replace the exact face region. -/
theorem unrelated_face_region_blocked
    (face : graph.Face) (wrong : Set EuclideanDimension.two.Spacetime)
    (different : frontier wrong ≠
      finiteBoundaryWordTrace graph.pathCurve graph.edgePath (graph.boundaryWord face))
    (claimed : wrong = graph.faceRegion face) : False := by
  apply different
  rw [claimed]
  exact graph.face_frontier face

/-- Face-free embedded graphs remain legitimate: their trace complement is exactly the unbounded
region rather than being rejected by a false face-nonemptiness requirement. -/
theorem faceFree_complement_eq_unbounded [IsEmpty graph.Face] :
    (finiteEmbeddedGraphTrace graph.Edge graph.pathCurve graph.edgePath)ᶜ =
      graph.unboundedRegion := by
  rw [graph.complement_decomposition]
  simp

end

end YangMills.Dimensions.TwoDimensionalSimpleBoundaryPlanarGraph.Probes
