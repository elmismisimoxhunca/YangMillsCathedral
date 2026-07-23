/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaClosedTriangularPresentation

/-! Hostile probes for closed Sengupta triangular presentations. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaClosedTriangularPresentation.Probes

open YangMills.Mathematics

noncomputable section

variable
    {Vertex Edge InternalEdge Face Region : Type*}
    [Fintype Edge] [DecidableEq Edge]
    [Fintype InternalEdge] [DecidableEq InternalEdge]
    [Fintype Face] [DecidableEq Face] [DecidableEq Region]
    {triangulation : TwoDimensionalSenguptaTriangulatedRegionData
      Edge InternalEdge Face Region}
    (data : TwoDimensionalSenguptaClosedTriangularPresentationData
      (Vertex := Vertex) triangulation)

omit [Fintype Edge] [Fintype InternalEdge] in
/-- Candidate three-traversal words are now required to be closed and cyclically composable. -/
theorem exact_closed_composable_face (face : Face) :
    IsSenguptaClosedComposableTriangle data.edgeInitial data.edgeTerminal
      (triangulation.boundaryWord face) :=
  data.face_closed_composable face

omit [Fintype Edge] [Fintype InternalEdge] in
include data in
/-- Hostile probe: a repeated underlying side is impossible in any certified face. -/
theorem repeated_first_second_side_blocked (face : Face)
    (first second third : OrientedEdge (Sum Edge InternalEdge))
    (word : triangulation.boundaryWord face = [first, second, third])
    (repeated : OrientedEdge.underlying first = OrientedEdge.underlying second) : False := by
  obtain ⟨first', second', third', certified, _, _, _, distinct, _⟩ :=
    data.face_closed_composable face
  rw [word] at certified
  simp only [List.cons.injEq, and_true] at certified
  obtain ⟨rfl, rfl, rfl⟩ := certified
  exact distinct repeated

omit [Fintype Edge] [Fintype InternalEdge] in
include data in
/-- Hostile probe: changing the orientation-independent two-face incidence destroys the
internal-edge certificate. -/
theorem changed_internal_incidence_blocked (edge : InternalEdge)
    (changed :
      (∑ face : Face, (triangulation.boundaryWord face).countP
        (fun oriented => decide (OrientedEdge.underlying oriented = Sum.inr edge))) ≠ 2) : False :=
  changed (data.internal_incidence_count edge)

omit [Fintype Edge] [Fintype InternalEdge] in
include data in
/-- Every internal edge has exactly two incidences, without imposing global orientation coherence. -/
theorem exact_internal_two_face_incidence (edge : InternalEdge) :
    (∑ face : Face, (triangulation.boundaryWord face).countP
      (fun oriented => decide (OrientedEdge.underlying oriented = Sum.inr edge))) = 2 :=
  data.internal_incidence_count edge

omit [Fintype Edge] [Fintype InternalEdge] in
include data in
/-- An empty face carrier cannot certify a two-dimensional presentation. -/
theorem empty_face_presentation_blocked (emptyFace : IsEmpty Face) : False :=
  emptyFace.false data.face_nonempty.some

omit [Fintype Edge] [Fintype InternalEdge] in
include data in
/-- Hostile probe: an unused external graph edge is forbidden. -/
theorem unused_external_edge_blocked (edge : Edge)
    (unused : ∀ face : Face, ∀ oriented ∈ triangulation.boundaryWord face,
      OrientedEdge.underlying oriented ≠ Sum.inl edge) : False := by
  obtain ⟨face, oriented, member, underlying⟩ := data.externalEdge_used edge
  exact unused face oriented member underlying

omit [Fintype Edge] [Fintype InternalEdge] in
/-- Degenerate loop edges are forbidden before any face is considered. -/
theorem loop_edge_blocked (edge : Sum Edge InternalEdge)
    (loop : data.edgeInitial edge = data.edgeTerminal edge) : False :=
  data.edge_endpoints_ne edge loop

end

end YangMills.Dimensions.TwoDimensionalSenguptaClosedTriangularPresentation.Probes
