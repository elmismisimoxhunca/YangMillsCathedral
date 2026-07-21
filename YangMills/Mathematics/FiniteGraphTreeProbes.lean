/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteGraphTree

/-!
# Probes for finite graph trees and frozen product Haar
-/

namespace YangMills.Mathematics.FiniteGraphTree.Probes

open MeasureTheory

noncomputable section

universe uVertex uEdge uG

/-- The exact no-distinct-edge-loop clause is exposed directly. -/
theorem exact_tree_rejects_supported_simple_loop
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) (tree : Finset Edge)
    (isTree : FiniteGraphEdgeSetIsTree edgeSource edgeTarget tree)
    (word : List (OrientedEdge Edge)) (root : Vertex)
    (nonempty : word ≠ [])
    (closed : OrientedEdgeWordRunsFrom edgeSource edgeTarget word root root)
    (distinct : word.Pairwise (fun first second =>
      OrientedEdge.underlying first ≠ OrientedEdge.underlying second))
    (supported : ∀ oriented ∈ word, OrientedEdge.underlying oriented ∈ tree) : False :=
  isTree word root nonempty closed distinct supported

/-- A genuinely non-loop singleton is a nonempty tree, preventing empty-only semantics. -/
theorem nonloop_singleton_is_tree
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) (edge : Edge)
    (not_loop : edgeSource edge ≠ edgeTarget edge) :
    FiniteGraphEdgeSetIsTree edgeSource edgeTarget {edge} :=
  finiteGraphEdgeSetIsTree_singleton edgeSource edgeTarget edge not_loop

/-- Traversing one edge forward and back is not a distinct-underlying-edge simple loop, so it does
not invalidate the singleton tree. -/
theorem forward_reverse_reuse_fails_distinctness
    {Edge : Type uEdge} (edge : Edge) :
    ¬ [OrientedEdge.forward edge, OrientedEdge.reverse edge].Pairwise
      (fun first second =>
        OrientedEdge.underlying first ≠ OrientedEdge.underlying second) := by
  simp

/-- A graph loop cannot be smuggled in as a one-edge tree. -/
theorem loop_singleton_not_tree
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) (edge : Edge)
    (loop : edgeSource edge = edgeTarget edge) :
    ¬ FiniteGraphEdgeSetIsTree edgeSource edgeTarget {edge} := by
  intro isTree
  apply isTree [.forward edge] (edgeSource edge)
  · simp
  · right
    refine ⟨by simp, ?_, rfl, ?_⟩
    · simp
    · simpa [OrientedEdge.target] using loop.symm
  · simp
  · intro oriented membership
    simp at membership
    subst oriented
    simp

/-- The empty tree freezes no coordinates and recovers exact product Haar. -/
theorem empty_tree_measure_eq_productHaar
    (Edge : Type uEdge) [Fintype Edge] [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    finiteTreeFrozenProductMeasure Edge G ∅ =
      normalizedCompactHaarFiniteProductMeasure Edge G :=
  finiteTreeFrozenProductMeasure_empty Edge G

/-- Membership forces the identity Dirac coordinate, not Haar. -/
theorem exact_frozen_coordinate
    {Edge : Type uEdge} [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) (membership : edge ∈ tree) :
    finiteTreeFrozenCoordinateMeasure G tree edge = Measure.dirac 1 :=
  finiteTreeFrozenCoordinateMeasure_of_mem G tree edge membership

/-- Nonmembership forces unchanged canonical normalized Haar. -/
theorem exact_unfrozen_coordinate
    {Edge : Type uEdge} [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) (not_membership : edge ∉ tree) :
    finiteTreeFrozenCoordinateMeasure G tree edge = normalizedCompactHaarMeasure G :=
  finiteTreeFrozenCoordinateMeasure_of_not_mem G tree edge not_membership

/-- Replacing a genuinely frozen coordinate by a distinct proposed law is rejected. -/
theorem wrong_frozen_coordinate_blocked
    {Edge : Type uEdge} [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) (membership : edge ∈ tree)
    (wrong : Measure G) (different : wrong ≠ Measure.dirac 1)
    (claimed : finiteTreeFrozenCoordinateMeasure G tree edge = wrong) : False := by
  apply different
  rw [← claimed]
  exact finiteTreeFrozenCoordinateMeasure_of_mem G tree edge membership

end

end YangMills.Mathematics.FiniteGraphTree.Probes
