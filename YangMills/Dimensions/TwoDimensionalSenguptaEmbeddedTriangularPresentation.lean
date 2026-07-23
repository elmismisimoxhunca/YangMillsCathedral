/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaClosedTriangularPresentation
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Embedded triangular presentations for Sengupta finite-face data

This file states the previously missing topological realization obligation. Vertices, embedded unit
interval edges, and embedded closed-disk faces cover one compact connected two-manifold. Face
boundaries are exactly the edge images named by the oriented boundary words; open face cells are
pairwise disjoint and avoid the one-skeleton; open edge cells are pairwise disjoint and avoid all
vertices.

The structure is intentionally uninhabited. It is an acceptance surface for an actual embedded
finite triangular presentation of a Definition 7.2 pair: the nonempty finite curve family has
composable globally distinct bonds, the finite region family is exactly the maximal connected
partition of its complement, same-region and empty-curve face chains are explicit, face
intersections are common simplices, and marked circle sides follow the oriented boundary words.
Orientable complexes force coherent stored face orientations; nonorientable complexes retain
arbitrary face orientations. This is not a theorem that every candidate presentation has such a
realization and not a universal subdivision/homeomorphism result.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open Set Metric
open scoped Manifold ContDiff

noncomputable section

universe uSurface uVertex uEdge uInternal uFace uRegion uCurve

/-- Closed Euclidean unit disk used as the carrier of one embedded face. -/
abbrev SenguptaClosedUnitDisk :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- Open Euclidean unit disk used for the interior of one embedded face. -/
abbrev SenguptaOpenUnitDisk :=
  Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- Unit circle used as the boundary carrier of one embedded face. -/
abbrev SenguptaUnitCircle :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- Closed unit interval used as the carrier of one embedded edge. -/
abbrev SenguptaClosedUnitInterval := Set.Icc (0 : ℝ) 1

/-- Open unit interval used for the interior of one embedded edge. -/
abbrev SenguptaOpenUnitInterval := Set.Ioo (0 : ℝ) 1

/-- Include the open disk into the closed disk. -/
def senguptaOpenDiskToClosedDisk : SenguptaOpenUnitDisk → SenguptaClosedUnitDisk :=
  fun point => ⟨point, Metric.mem_closedBall.mpr
    (le_of_lt (Metric.mem_ball.mp point.property))⟩

/-- Include the unit circle into the closed disk. -/
def senguptaCircleToClosedDisk : SenguptaUnitCircle → SenguptaClosedUnitDisk :=
  fun point => ⟨point, le_of_eq point.property⟩

/-- Include the open interval into the closed interval. -/
def senguptaOpenIntervalToClosedInterval :
    SenguptaOpenUnitInterval → SenguptaClosedUnitInterval :=
  fun point => ⟨point, ⟨le_of_lt point.property.1, le_of_lt point.property.2⟩⟩

/-- Reverse the closed unit interval. -/
def senguptaReverseClosedUnitInterval :
    SenguptaClosedUnitInterval → SenguptaClosedUnitInterval :=
  fun point => ⟨1 - point, by constructor <;> linarith [point.property.1, point.property.2]⟩

/-- Evaluate an embedded edge with the orientation stored in a boundary or curve word. -/
def senguptaOrientedEmbeddedEdgePath
    {Edge Surface : Type*} (edgePath : Edge → SenguptaClosedUnitInterval → Surface) :
    OrientedEdge Edge → SenguptaClosedUnitInterval → Surface
  | .forward edge => edgePath edge
  | .reverse edge => fun point => edgePath edge (senguptaReverseClosedUnitInterval point)

/-- Consecutive oriented edges in one source path have matching endpoints. -/
def IsSenguptaComposableOrientedPath
    {Vertex Edge : Type*} (edgeInitial edgeTerminal : Edge → Vertex) :
    List (OrientedEdge Edge) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      senguptaOrientedEdgeTerminal edgeInitial edgeTerminal first =
        senguptaOrientedEdgeInitial edgeInitial edgeTerminal second ∧
      IsSenguptaComposableOrientedPath edgeInitial edgeTerminal (second :: rest)

/-- Trace of the external graph edges carrying Sengupta's path family. -/
def senguptaEmbeddedCurveTrace
    {Edge InternalEdge Surface : Type*}
    (edgePath : Sum Edge InternalEdge → SenguptaClosedUnitInterval → Surface) : Set Surface :=
  ⋃ edge : Edge, Set.range (edgePath (Sum.inl edge))

/-- Two faces share an internal edge of the finite presentation. -/
def SenguptaFacesShareInternalEdge
    {Edge InternalEdge Face Region : Type*}
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region) (face₁ face₂ : Face) : Prop :=
  ∃ internal : InternalEdge, ∃ oriented₁ ∈ triangulation.boundaryWord face₁,
    ∃ oriented₂ ∈ triangulation.boundaryWord face₂,
      OrientedEdge.underlying oriented₁ = Sum.inr internal ∧
      OrientedEdge.underlying oriented₂ = Sum.inr internal

/-- Two faces share any simplicial edge. -/
def SenguptaFacesShareEdge
    {Edge InternalEdge Face Region : Type*}
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region) (face₁ face₂ : Face) : Prop :=
  ∃ edge : Sum Edge InternalEdge, ∃ oriented₁ ∈ triangulation.boundaryWord face₁,
    ∃ oriented₂ ∈ triangulation.boundaryWord face₂,
      OrientedEdge.underlying oriented₁ = edge ∧
      OrientedEdge.underlying oriented₂ = edge

/-- Coherent orientations use each edge once in each direction across all face boundaries. -/
def AreSenguptaFaceBoundaryOrientationsCoherent
    {Edge InternalEdge Face : Type*} [Fintype Face]
    [DecidableEq Edge] [DecidableEq InternalEdge]
    (boundaryWord : Face → List (OrientedEdge (Sum Edge InternalEdge))) : Prop :=
  ∀ edge : Sum Edge InternalEdge,
    (∑ face : Face, (boundaryWord face).count (.forward edge)) = 1 ∧
    (∑ face : Face, (boundaryWord face).count (.reverse edge)) = 1

/-- Reverse selected face words when testing combinatorial orientability. -/
def senguptaMaybeReverseFaceWord
    {Edge Face : Type*} (reverseFace : Face → Bool)
    (boundaryWord : Face → List (OrientedEdge Edge)) (face : Face) :
    List (OrientedEdge Edge) :=
  if reverseFace face then reverseFiniteOrientedWord (boundaryWord face) else boundaryWord face

/-- A finite triangular complex is combinatorially orientable when face orientations can be selected
so that every edge receives opposite induced orientations from its two incident faces. -/
def IsSenguptaCombinatoriallyOrientable
    {Edge InternalEdge Face Region : Type*}
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    [DecidableEq Edge] [DecidableEq InternalEdge]
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region) : Prop :=
  ∃ reverseFace : Face → Bool,
    AreSenguptaFaceBoundaryOrientationsCoherent
      (senguptaMaybeReverseFaceWord reverseFace triangulation.boundaryWord)

variable
    {Surface : Type uSurface}
    [TopologicalSpace Surface]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Surface]
    {Vertex : Type uVertex}
    {Curve : Type uCurve} [Fintype Curve]
    {Edge : Type uEdge} [DecidableEq Edge]
    {InternalEdge : Type uInternal} [DecidableEq InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    {closed : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation}

/-- The `i`th oriented side of a certified three-side face boundary. -/
def senguptaTriangleBoundaryEdgeAt (face : Face) (i : Fin 3) :
    OrientedEdge (Sum Edge InternalEdge) :=
  (triangulation.boundaryWord face).get
    ⟨i, by simp [closed.boundaryWord_length_three face, i.isLt]⟩

/-- An actual finite embedded triangular cell presentation of one compact connected two-manifold. -/
structure TwoDimensionalSenguptaEmbeddedTriangularPresentationData where
  surface_t2 : T2Space Surface
  surface_compact : CompactSpace Surface
  surface_connected : ConnectedSpace Surface
  surface_twoManifold :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞ Surface
  curve_nonempty : Nonempty Curve
  region_finite : Fintype Region
  vertexPoint : Vertex → Surface
  vertexPoint_injective : Function.Injective vertexPoint
  edgePath : Sum Edge InternalEdge → SenguptaClosedUnitInterval → Surface
  edgePath_embedding : ∀ edge, Topology.IsEmbedding (edgePath edge)
  edgePath_initial : ∀ edge,
    edgePath edge ⟨0, by norm_num⟩ = vertexPoint (closed.edgeInitial edge)
  edgePath_terminal : ∀ edge,
    edgePath edge ⟨1, by norm_num⟩ = vertexPoint (closed.edgeTerminal edge)
  curveWord : Curve → List (OrientedEdge Edge)
  curveWord_nonempty : ∀ curve, curveWord curve ≠ []
  curveWord_composable : ∀ curve,
    IsSenguptaComposableOrientedPath
      (fun edge => closed.edgeInitial (Sum.inl edge))
      (fun edge => closed.edgeTerminal (Sum.inl edge)) (curveWord curve)
  /-- Sengupta's globally distinct curve bonds: every external edge occurs in exactly one curve word. -/
  curveEdge_count : ∀ edge : Edge,
    ∑ curve : Curve, (curveWord curve).countP
      (fun oriented => decide (OrientedEdge.underlying oriented = edge)) = 1
  /-- Every simplicial edge, including a curve edge, has exactly two face incidences. -/
  allEdge_faceIncidence_count : ∀ edge : Sum Edge InternalEdge,
    ∑ face : Face, (triangulation.boundaryWord face).countP
      (fun oriented => decide (OrientedEdge.underlying oriented = edge)) = 2
  /-- On a combinatorially orientable realization, the stored source boundary words themselves use
  the coherent global orientation required in Sengupta 7.6. In the nonorientable case arbitrary
  individual face orientations remain permitted. -/
  boundaryOrientation_coherent_if_orientable :
    IsSenguptaCombinatoriallyOrientable triangulation →
      AreSenguptaFaceBoundaryOrientationsCoherent triangulation.boundaryWord
  edgeInterior_pairwise_disjoint : ∀ edge₁ edge₂, edge₁ ≠ edge₂ →
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitInterval =>
        edgePath edge₁ (senguptaOpenIntervalToClosedInterval point)))
      (Set.range (fun point : SenguptaOpenUnitInterval =>
        edgePath edge₂ (senguptaOpenIntervalToClosedInterval point)))
  edgeInterior_avoids_vertices : ∀ edge,
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitInterval =>
        edgePath edge (senguptaOpenIntervalToClosedInterval point)))
      (Set.range vertexPoint)
  faceDisk : Face → SenguptaClosedUnitDisk → Surface
  faceDisk_embedding : ∀ face, Topology.IsEmbedding (faceDisk face)
  faceSideParam : Face → Fin 3 → SenguptaClosedUnitInterval → SenguptaUnitCircle
  faceSideParam_embedding : ∀ face side, Topology.IsEmbedding (faceSideParam face side)
  faceSideRanges_cover : ∀ face,
    (⋃ side : Fin 3, Set.range (faceSideParam face side)) = Set.univ
  faceSide_orientedPath : ∀ face side point,
    faceDisk face (senguptaCircleToClosedDisk (faceSideParam face side point)) =
      senguptaOrientedEmbeddedEdgePath edgePath
        (senguptaTriangleBoundaryEdgeAt (triangulation := triangulation)
          (closed := closed) face side) point
  faceBoundary_eq_edgeImages : ∀ face,
    Set.range (fun point : SenguptaUnitCircle =>
      faceDisk face (senguptaCircleToClosedDisk point)) =
    ⋃ (oriented : OrientedEdge (Sum Edge InternalEdge))
      (_ : oriented ∈ triangulation.boundaryWord face),
      Set.range (edgePath (OrientedEdge.underlying oriented))
  faceInterior_pairwise_disjoint : ∀ face₁ face₂, face₁ ≠ face₂ →
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        faceDisk face₁ (senguptaOpenDiskToClosedDisk point)))
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        faceDisk face₂ (senguptaOpenDiskToClosedDisk point)))
  faceInterior_avoids_oneSkeleton : ∀ face,
    Disjoint
      (Set.range (fun point : SenguptaOpenUnitDisk =>
        faceDisk face (senguptaOpenDiskToClosedDisk point)))
      ((Set.range vertexPoint) ∪
        ⋃ edge : Sum Edge InternalEdge, Set.range (edgePath edge))
  /-- Distinct closed faces meet in no simplex, one common vertex, or one common edge. -/
  faceIntersection_commonSimplex : ∀ face₁ face₂, face₁ ≠ face₂ →
    Set.range (faceDisk face₁) ∩ Set.range (faceDisk face₂) = ∅ ∨
    (∃ vertex : Vertex,
      Set.range (faceDisk face₁) ∩ Set.range (faceDisk face₂) = {vertexPoint vertex}) ∨
    ∃ edge : Sum Edge InternalEdge,
      (∃ oriented ∈ triangulation.boundaryWord face₁,
        OrientedEdge.underlying oriented = edge) ∧
      (∃ oriented ∈ triangulation.boundaryWord face₂,
        OrientedEdge.underlying oriented = edge) ∧
      Set.range (faceDisk face₁) ∩ Set.range (faceDisk face₂) = Set.range (edgePath edge)
  faceImages_cover :
    (⋃ face : Face, Set.range (faceDisk face)) = Set.univ
  regionSet : Region → Set Surface
  regionSet_connected : ∀ region, IsConnected (regionSet region)
  regionSet_subset_curveComplement : ∀ region,
    regionSet region ⊆ (senguptaEmbeddedCurveTrace edgePath)ᶜ
  regionSet_pairwise_disjoint : ∀ region₁ region₂, region₁ ≠ region₂ →
    Disjoint (regionSet region₁) (regionSet region₂)
  regionSets_cover_curveComplement :
    (⋃ region : Region, regionSet region) = (senguptaEmbeddedCurveTrace edgePath)ᶜ
  /-- Each listed connected region is maximal among connected subsets of the curve complement. -/
  regionSet_maximal : ∀ (region : Region) (subset : Set Surface),
    IsConnected subset → subset ⊆ (senguptaEmbeddedCurveTrace edgePath)ᶜ →
    (subset ∩ regionSet region).Nonempty → subset ⊆ regionSet region
  faceInterior_region : ∀ face,
    Set.range (fun point : SenguptaOpenUnitDisk =>
      faceDisk face (senguptaOpenDiskToClosedDisk point)) ⊆
      regionSet (triangulation.faceRegion face)
  /-- Sengupta 7.2 connectivity by successive shared non-curve (internal) edges. -/
  sameRegion_faceChain : ∀ face₁ face₂,
    triangulation.faceRegion face₁ = triangulation.faceRegion face₂ →
    Relation.ReflTransGen (SenguptaFacesShareInternalEdge triangulation) face₁ face₂
  /-- The additional Definition 7.2 hypothesis with the curve family replaced by the empty family. -/
  allFaces_faceChain : ∀ face₁ face₂,
    Relation.ReflTransGen (SenguptaFacesShareEdge triangulation) face₁ face₂

namespace TwoDimensionalSenguptaEmbeddedTriangularPresentationData

/-- Every embedded face image is nonempty. -/
theorem faceImage_nonempty
    (data : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := closed)) (face : Face) :
    (Set.range (data.faceDisk face)).Nonempty :=
  ⟨data.faceDisk face ⟨0, by simp [SenguptaClosedUnitDisk]⟩, ⟨_, rfl⟩⟩

/-- The embedded face family really covers every surface point. -/
theorem exists_face_containing
    (data : TwoDimensionalSenguptaEmbeddedTriangularPresentationData
      (Surface := Surface) (Curve := Curve) (closed := closed)) (point : Surface) :
    ∃ face : Face, point ∈ Set.range (data.faceDisk face) := by
  have member : point ∈ (⋃ face : Face, Set.range (data.faceDisk face)) := by
    rw [data.faceImages_cover]
    exact Set.mem_univ point
  simpa only [Set.mem_iUnion] using member

end TwoDimensionalSenguptaEmbeddedTriangularPresentationData

end

end YangMills.Dimensions
