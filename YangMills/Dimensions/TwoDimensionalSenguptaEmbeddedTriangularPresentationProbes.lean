/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedTriangularPresentation

/-! Hostile probes for embedded Sengupta triangular presentations. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedTriangularPresentation.Probes

open YangMills.Mathematics
open Set Metric
open scoped Manifold ContDiff

noncomputable section

variable
    {Surface Vertex Edge InternalEdge Face Region Curve : Type*}
    [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    [DecidableEq Edge] [DecidableEq InternalEdge]
    [Fintype Face] [DecidableEq Face]
    [DecidableEq Region] [Fintype Curve]
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {closed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation}
    (data : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := closed))

include data in
/-- Compactness, connectedness, Hausdorff separation, and two-manifold semantics are load-bearing
fields, not comments inferred from a cell cover. -/
theorem exact_surface_semantics :
    Nonempty (T2Space Surface) ∧ Nonempty (CompactSpace Surface) ∧
    Nonempty (ConnectedSpace Surface) ∧
    Nonempty (IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞ Surface) :=
  ⟨⟨data.surface_t2⟩, ⟨data.surface_compact⟩, ⟨data.surface_connected⟩,
    ⟨data.surface_twoManifold⟩⟩

include data in
/-- The source curve family is nonempty and the complement-region carrier is explicitly finite. -/
theorem exact_source_carriers : Nonempty Curve ∧ Nonempty (Fintype Region) :=
  ⟨data.curve_nonempty, ⟨data.region_finite⟩⟩

/-- Edge endpoints are exactly the vertices specified by the closed incidence presentation. -/
theorem exact_edge_endpoints (edge : Sum Edge InternalEdge) :
    data.edgePath edge ⟨0, by norm_num⟩ = data.vertexPoint (closed.edgeInitial edge) ∧
    data.edgePath edge ⟨1, by norm_num⟩ = data.vertexPoint (closed.edgeTerminal edge) :=
  ⟨data.edgePath_initial edge, data.edgePath_terminal edge⟩

/-- Every face boundary is exactly, not merely contained in, its three named edge images. -/
theorem exact_face_boundary (face : Face) :
    Set.range (fun point : SenguptaUnitCircle =>
      data.faceDisk face (senguptaCircleToClosedDisk point)) =
    ⋃ (oriented : OrientedEdge (Sum Edge InternalEdge))
      (_ : oriented ∈ triangulation.boundaryWord face),
      Set.range (data.edgePath (OrientedEdge.underlying oriented)) :=
  data.faceBoundary_eq_edgeImages face

/-- Hostile boundary probe: changing the edge realization cannot preserve certification. -/
theorem changed_face_boundary_blocked (face : Face)
    (changed : Set.range (fun point : SenguptaUnitCircle =>
      data.faceDisk face (senguptaCircleToClosedDisk point)) ≠
    ⋃ (oriented : OrientedEdge (Sum Edge InternalEdge))
      (_ : oriented ∈ triangulation.boundaryWord face),
      Set.range (data.edgePath (OrientedEdge.underlying oriented))) : False :=
  changed (data.faceBoundary_eq_edgeImages face)

/-- Hostile coverage probe: omitting any surface point contradicts the exact finite face cover. -/
theorem uncovered_surface_point_blocked (point : Surface)
    (uncovered : ∀ face : Face, point ∉ Set.range (data.faceDisk face)) : False := by
  obtain ⟨face, member⟩ := data.exists_face_containing point
  exact uncovered face member

/-- Distinct open face cells are forced to be disjoint. -/
theorem exact_face_interior_disjoint (face₁ face₂ : Face) (different : face₁ ≠ face₂) :
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        data.faceDisk face₁ (senguptaOpenDiskToClosedDisk point)))
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        data.faceDisk face₂ (senguptaOpenDiskToClosedDisk point))) :=
  data.faceInterior_pairwise_disjoint face₁ face₂ different

/-- Distinct open edge cells are forced to be disjoint. -/
theorem exact_edge_interior_disjoint (edge₁ edge₂ : Sum Edge InternalEdge)
    (different : edge₁ ≠ edge₂) :
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitInterval =>
        data.edgePath edge₁ (senguptaOpenIntervalToClosedInterval point)))
      (Set.range (fun point : SenguptaOpenUnitInterval =>
        data.edgePath edge₂ (senguptaOpenIntervalToClosedInterval point))) :=
  data.edgeInterior_pairwise_disjoint edge₁ edge₂ different

/-- Vertex injectivity and both embedding families are explicit realization obligations. -/
theorem exact_embedding_semantics (vertex₁ vertex₂ : Vertex)
    (equalImage : data.vertexPoint vertex₁ = data.vertexPoint vertex₂)
    (edge : Sum Edge InternalEdge) (face : Face) :
    vertex₁ = vertex₂ ∧ Topology.IsEmbedding (data.edgePath edge) ∧
      Topology.IsEmbedding (data.faceDisk face) :=
  ⟨data.vertexPoint_injective equalImage, data.edgePath_embedding edge,
    data.faceDisk_embedding face⟩

/-- Open cells have the exact advertised avoidance from lower-dimensional skeleta. -/
theorem exact_cell_avoidance (edge : Sum Edge InternalEdge) (face : Face) :
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitInterval =>
        data.edgePath edge (senguptaOpenIntervalToClosedInterval point)))
      (Set.range data.vertexPoint) ∧
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        data.faceDisk face (senguptaOpenDiskToClosedDisk point)))
      ((Set.range data.vertexPoint) ∪
        ⋃ edge : Sum Edge InternalEdge, Set.range (data.edgePath edge)) :=
  ⟨data.edgeInterior_avoids_vertices edge, data.faceInterior_avoids_oneSkeleton face⟩

/-- Hostile avoidance probe: permitting an open face cell to meet the one-skeleton is rejected. -/
theorem changed_face_avoidance_blocked (face : Face)
    (changed : ¬ Disjoint
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        data.faceDisk face (senguptaOpenDiskToClosedDisk point)))
      ((Set.range data.vertexPoint) ∪
        ⋃ edge : Sum Edge InternalEdge, Set.range (data.edgePath edge))) : False :=
  changed (data.faceInterior_avoids_oneSkeleton face)

/-- Marked side parametrizations are embedded and jointly cover the entire face circle. -/
theorem exact_marked_side_geometry (face : Face) (side : Fin 3) :
    Topology.IsEmbedding (data.faceSideParam face side) ∧
      (⋃ side : Fin 3, Set.range (data.faceSideParam face side)) = Set.univ :=
  ⟨data.faceSideParam_embedding face side, data.faceSideRanges_cover face⟩

/-- Each marked circle side follows the corresponding boundary word edge with its exact orientation. -/
theorem exact_oriented_side_restriction (face : Face) (side : Fin 3)
    (point : SenguptaClosedUnitInterval) :
    data.faceDisk face (senguptaCircleToClosedDisk (data.faceSideParam face side point)) =
      senguptaOrientedEmbeddedEdgePath data.edgePath
        (senguptaTriangleBoundaryEdgeAt (triangulation := triangulation)
          (closed := closed) face side) point :=
  data.faceSide_orientedPath face side point

/-- Distinct face intersections are certified common simplices, not arbitrary boundary subsets. -/
theorem exact_simplicial_face_intersection (face₁ face₂ : Face) (different : face₁ ≠ face₂) :
    Set.range (data.faceDisk face₁) ∩ Set.range (data.faceDisk face₂) = ∅ ∨
    (∃ vertex : Vertex,
      Set.range (data.faceDisk face₁) ∩ Set.range (data.faceDisk face₂) =
        {data.vertexPoint vertex}) ∨
    ∃ edge : Sum Edge InternalEdge,
      (∃ oriented ∈ triangulation.boundaryWord face₁,
        OrientedEdge.underlying oriented = edge) ∧
      (∃ oriented ∈ triangulation.boundaryWord face₂,
        OrientedEdge.underlying oriented = edge) ∧
      Set.range (data.faceDisk face₁) ∩ Set.range (data.faceDisk face₂) =
        Set.range (data.edgePath edge) :=
  data.faceIntersection_commonSimplex face₁ face₂ different

/-- The path family uses each external bond exactly once and is composable. -/
theorem exact_curve_path (curve : Curve) (edge : Edge) :
    data.curveWord curve ≠ [] ∧
    IsSenguptaComposableOrientedPath
      (fun edge => closed.edgeInitial (Sum.inl edge))
      (fun edge => closed.edgeTerminal (Sum.inl edge)) (data.curveWord curve) ∧
    (∑ curve : Curve, (data.curveWord curve).countP
      (fun oriented => decide (OrientedEdge.underlying oriented = edge))) = 1 :=
  ⟨data.curveWord_nonempty curve, data.curveWord_composable curve,
    data.curveEdge_count edge⟩

include data in
/-- Every simplicial edge has two face incidences, and orientable complexes force the stored words
to be globally coherent. -/
theorem exact_simplicial_incidence_and_orientation (edge : Sum Edge InternalEdge)
    (orientable : IsSenguptaCombinatoriallyOrientable triangulation) :
    (∑ face : Face, (triangulation.boundaryWord face).countP
      (fun oriented => decide (OrientedEdge.underlying oriented = edge))) = 2 ∧
    AreSenguptaFaceBoundaryOrientationsCoherent triangulation.boundaryWord :=
  ⟨data.allEdge_faceIncidence_count edge,
    data.boundaryOrientation_coherent_if_orientable orientable⟩

/-- Region labels are exact connected components of the external curve complement at the stated
maximal-connected-set semantics, and face interiors use their stored labels. -/
theorem exact_region_semantics (region : Region) (face : Face) :
    IsConnected (data.regionSet region) ∧
    data.regionSet region ⊆ (senguptaEmbeddedCurveTrace data.edgePath)ᶜ ∧
    Set.range (fun point : SenguptaOpenUnitDisk =>
      data.faceDisk face (senguptaOpenDiskToClosedDisk point)) ⊆
      data.regionSet (triangulation.faceRegion face) :=
  ⟨data.regionSet_connected region, data.regionSet_subset_curveComplement region,
    data.faceInterior_region face⟩

/-- Distinct region labels denote disjoint complement components. -/
theorem exact_region_pairwise_disjoint (region₁ region₂ : Region)
    (different : region₁ ≠ region₂) :
    Disjoint (data.regionSet region₁) (data.regionSet region₂) :=
  data.regionSet_pairwise_disjoint region₁ region₂ different

/-- The finite regions cover the exact curve complement and are maximal connected pieces. -/
theorem exact_region_component_partition (region : Region) (subset : Set Surface)
    (connected : IsConnected subset)
    (inComplement : subset ⊆ (senguptaEmbeddedCurveTrace data.edgePath)ᶜ)
    (meets : (subset ∩ data.regionSet region).Nonempty) :
    (⋃ region : Region, data.regionSet region) =
        (senguptaEmbeddedCurveTrace data.edgePath)ᶜ ∧
      subset ⊆ data.regionSet region :=
  ⟨data.regionSets_cover_curveComplement,
    data.regionSet_maximal region subset connected inComplement meets⟩

include data in
/-- Same-region faces satisfy Sengupta's successive non-curve-edge connectivity. -/
theorem exact_same_region_face_chain (face₁ face₂ : Face)
    (same : triangulation.faceRegion face₁ = triangulation.faceRegion face₂) :
    Relation.ReflTransGen (SenguptaFacesShareInternalEdge triangulation) face₁ face₂ :=
  data.sameRegion_faceChain face₁ face₂ same

include data in
/-- Definition 7.2's additional empty-curve-family face-chain condition is explicit. -/
theorem exact_all_faces_chain (face₁ face₂ : Face) :
    Relation.ReflTransGen (SenguptaFacesShareEdge triangulation) face₁ face₂ :=
  data.allFaces_faceChain face₁ face₂

end

end YangMills.Dimensions.TwoDimensionalSenguptaEmbeddedTriangularPresentation.Probes
