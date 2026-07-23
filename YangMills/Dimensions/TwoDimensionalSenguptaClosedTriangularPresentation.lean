/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors

/-!
# Closed triangular presentations for Sengupta finite-face factors

`TwoDimensionalSenguptaTriangulatedRegionData` deliberately records only three traversals per face.
This file adds the missing finite incidence geometry: endpoints, cyclic composability and closure,
three distinct underlying sides, orientation-independent two-face incidence for every internal edge,
a nonempty face carrier, and use of every external edge. No global orientation coherence is imposed,
so nonorientable source presentations are not excluded.

This is still combinatorial. It does not assert that the resulting finite complex is embedded in, or
homeomorphic to, the compact surface in Sengupta Definition 7.6.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics

noncomputable section

universe uVertex uEdge uInternal uFace uRegion

/-- Initial vertex of an oriented edge. -/
def senguptaOrientedEdgeInitial
    {Vertex : Type uVertex} {Edge : Type uEdge}
    (edgeInitial edgeTerminal : Edge → Vertex) : OrientedEdge Edge → Vertex
  | .forward edge => edgeInitial edge
  | .reverse edge => edgeTerminal edge

/-- Terminal vertex of an oriented edge. -/
def senguptaOrientedEdgeTerminal
    {Vertex : Type uVertex} {Edge : Type uEdge}
    (edgeInitial edgeTerminal : Edge → Vertex) : OrientedEdge Edge → Vertex
  | .forward edge => edgeTerminal edge
  | .reverse edge => edgeInitial edge

/-- A word is the cyclic boundary of a triangle with three distinct underlying sides. -/
def IsSenguptaClosedComposableTriangle
    {Vertex : Type uVertex} {Edge : Type uEdge}
    (edgeInitial edgeTerminal : Edge → Vertex) (word : List (OrientedEdge Edge)) : Prop :=
  ∃ first second third,
    word = [first, second, third] ∧
    senguptaOrientedEdgeTerminal edgeInitial edgeTerminal first =
      senguptaOrientedEdgeInitial edgeInitial edgeTerminal second ∧
    senguptaOrientedEdgeTerminal edgeInitial edgeTerminal second =
      senguptaOrientedEdgeInitial edgeInitial edgeTerminal third ∧
    senguptaOrientedEdgeTerminal edgeInitial edgeTerminal third =
      senguptaOrientedEdgeInitial edgeInitial edgeTerminal first ∧
    OrientedEdge.underlying first ≠ OrientedEdge.underlying second ∧
    OrientedEdge.underlying second ≠ OrientedEdge.underlying third ∧
    OrientedEdge.underlying third ≠ OrientedEdge.underlying first

variable
    {Vertex : Type uVertex}
    {Edge : Type uEdge} [Fintype Edge] [DecidableEq Edge]
    {InternalEdge : Type uInternal} [Fintype InternalEdge] [DecidableEq InternalEdge]
    {Face : Type uFace} [Fintype Face] [DecidableEq Face]
    {Region : Type uRegion} [DecidableEq Region]

/-- Finite closed triangular incidence data refining one heat-factor candidate presentation. -/
structure TwoDimensionalSenguptaClosedTriangularPresentationData
    (triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region) where
  face_nonempty : Nonempty Face
  edgeInitial : Sum Edge InternalEdge → Vertex
  edgeTerminal : Sum Edge InternalEdge → Vertex
  edge_endpoints_ne : ∀ edge, edgeInitial edge ≠ edgeTerminal edge
  face_closed_composable : ∀ face,
    IsSenguptaClosedComposableTriangle edgeInitial edgeTerminal
      (triangulation.boundaryWord face)
  /-- Every integrated edge is an interior side incident to exactly two triangular faces. Counts are
  orientation-independent because Sengupta permits arbitrary simplex orientations when the complex
  is nonorientable. -/
  internal_incidence_count : ∀ edge,
    ∑ face : Face, (triangulation.boundaryWord face).countP
      (fun oriented => decide (OrientedEdge.underlying oriented = Sum.inr edge)) = 2
  /-- No declared external graph edge is a dummy coordinate absent from all face boundaries. -/
  externalEdge_used : ∀ edge : Edge, ∃ face : Face, ∃ oriented,
    oriented ∈ triangulation.boundaryWord face ∧
      OrientedEdge.underlying oriented = Sum.inl edge

namespace TwoDimensionalSenguptaClosedTriangularPresentationData

omit [Fintype Edge] [Fintype InternalEdge] in
/-- Closure and cyclic composability recover the candidate's length-three condition independently. -/
theorem boundaryWord_length_three
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    (data : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation) (face : Face) :
    (triangulation.boundaryWord face).length = 3 := by
  obtain ⟨first, second, third, hword, _⟩ := data.face_closed_composable face
  simp [hword]

omit [Fintype Edge] [Fintype InternalEdge] in
/-- Every internal edge really occurs in a face boundary, with either orientation. -/
theorem exists_face_internal
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    (data : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation) (edge : InternalEdge) :
    ∃ face : Face, ∃ oriented ∈ triangulation.boundaryWord face,
      OrientedEdge.underlying oriented = Sum.inr edge := by
  by_contra absent
  push Not at absent
  have allZero : ∀ face : Face,
      (triangulation.boundaryWord face).countP
        (fun oriented => decide (OrientedEdge.underlying oriented = Sum.inr edge)) = 0 := by
    intro face
    rw [List.countP_eq_zero]
    intro oriented member
    simp [absent face oriented member]
  have : (∑ face : Face,
      (triangulation.boundaryWord face).countP
        (fun oriented => decide (OrientedEdge.underlying oriented = Sum.inr edge))) = 0 := by
    simp [allZero]
  rw [data.internal_incidence_count edge] at this
  omega

end TwoDimensionalSenguptaClosedTriangularPresentationData

end

end YangMills.Dimensions
