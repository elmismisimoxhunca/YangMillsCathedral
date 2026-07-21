/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteBoundaryConnectedWord
import YangMills.Mathematics.NormalizedCompactHaarFiniteProduct

/-!
# Finite graph trees and identity-frozen product Haar measures

Driver Definition 5.1 calls an orientation-stable bond subset a tree when it contains no nonempty
closed path whose unoriented bonds are all distinct. Because this project stores one coordinate per
underlying edge and derives both orientations, orientation stability is automatic. The predicate
below transcribes the remaining no-loop condition directly.

For such an underlying-edge set, Driver's `D_T g` replaces Haar measure on every tree coordinate by
the Dirac mass at the group identity and retains Haar measure elsewhere. The constructions here are
finite graph/measure theory only and make no planar, continuum, or Yang--Mills claim.
-/

namespace YangMills.Mathematics

open MeasureTheory

noncomputable section

universe uVertex uEdge uG

/-- Driver's finite tree predicate: no nonempty closed composable oriented word supported in the
set may use each underlying edge at most once. The set need not be connected or spanning. -/
def FiniteGraphEdgeSetIsTree
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) (tree : Finset Edge) : Prop :=
  ∀ (word : List (OrientedEdge Edge)) (root : Vertex),
    word ≠ [] →
    OrientedEdgeWordRunsFrom edgeSource edgeTarget word root root →
    word.Pairwise (fun first second =>
      OrientedEdge.underlying first ≠ OrientedEdge.underlying second) →
    (∀ oriented ∈ word, OrientedEdge.underlying oriented ∈ tree) →
    False

/-- The empty underlying-edge set is a Driver tree. -/
theorem finiteGraphEdgeSetIsTree_empty
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) :
    FiniteGraphEdgeSetIsTree edgeSource edgeTarget ∅ := by
  intro word root nonempty _runs _distinct supported
  obtain ⟨oriented, membership⟩ := List.exists_mem_of_ne_nil word nonempty
  simpa using supported oriented membership

/-- A single non-loop underlying edge is a nonempty Driver tree. -/
theorem finiteGraphEdgeSetIsTree_singleton
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) (edge : Edge)
    (not_loop : edgeSource edge ≠ edgeTarget edge) :
    FiniteGraphEdgeSetIsTree edgeSource edgeTarget {edge} := by
  intro word root nonempty runs distinct supported
  cases word with
  | nil => exact nonempty rfl
  | cons first tail =>
    cases tail with
    | nil =>
      rw [OrientedEdgeWordRunsFrom] at runs
      rcases runs with empty | ⟨_wordNonempty, _chain, starts, finishes⟩
      · simp at empty
      · have underlying_mem := supported first (by simp)
        have underlying_eq : OrientedEdge.underlying first = edge := by
          simpa using underlying_mem
        cases first with
        | forward candidate =>
          simp at underlying_eq
          subst candidate
          simp [OrientedEdge.source, OrientedEdge.target] at starts finishes
          exact not_loop (starts.trans finishes.symm)
        | reverse candidate =>
          simp at underlying_eq
          subst candidate
          simp [OrientedEdge.source, OrientedEdge.target] at starts finishes
          exact not_loop (finishes.trans starts.symm)
    | cons second rest =>
      have first_mem := supported first (by simp)
      have second_mem := supported second (by simp)
      have first_eq : OrientedEdge.underlying first = edge := by simpa using first_mem
      have second_eq : OrientedEdge.underlying second = edge := by simpa using second_mem
      have different :
          OrientedEdge.underlying first ≠ OrientedEdge.underlying second :=
        (List.pairwise_cons.mp distinct).1 second (by simp)
      exact different (first_eq.trans second_eq.symm)

/-- Coordinate law for Driver's tree-frozen measure: identity Dirac on tree edges, canonical
normalized Haar on every other underlying edge. -/
noncomputable def finiteTreeFrozenCoordinateMeasure
    {Edge : Type uEdge} [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) : Measure G :=
  if edge ∈ tree then Measure.dirac 1 else normalizedCompactHaarMeasure G

/-- Exact finite product of the tree-frozen coordinate laws. -/
noncomputable def finiteTreeFrozenProductMeasure
    (Edge : Type uEdge) [Fintype Edge] [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) : Measure (Edge → G) :=
  Measure.pi (finiteTreeFrozenCoordinateMeasure G tree)

/-- A frozen tree coordinate has exactly the identity Dirac law. -/
theorem finiteTreeFrozenCoordinateMeasure_of_mem
    {Edge : Type uEdge} [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) (membership : edge ∈ tree) :
    finiteTreeFrozenCoordinateMeasure G tree edge = Measure.dirac 1 := by
  simp [finiteTreeFrozenCoordinateMeasure, membership]

/-- A coordinate outside the tree retains the canonical normalized Haar law. -/
theorem finiteTreeFrozenCoordinateMeasure_of_not_mem
    {Edge : Type uEdge} [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) (not_membership : edge ∉ tree) :
    finiteTreeFrozenCoordinateMeasure G tree edge = normalizedCompactHaarMeasure G := by
  simp [finiteTreeFrozenCoordinateMeasure, not_membership]

/-- Freezing the empty tree recovers the exact finite product Haar reference. -/
theorem finiteTreeFrozenProductMeasure_empty
    (Edge : Type uEdge) [Fintype Edge] [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    finiteTreeFrozenProductMeasure Edge G ∅ =
      normalizedCompactHaarFiniteProductMeasure Edge G := by
  unfold finiteTreeFrozenProductMeasure normalizedCompactHaarFiniteProductMeasure
  congr 1

/-- The exact tree-frozen finite product remains a probability measure. -/
theorem finiteTreeFrozenProductMeasure_univ
    (Edge : Type uEdge) [Fintype Edge] [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) : finiteTreeFrozenProductMeasure Edge G tree Set.univ = 1 := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  letI (edge : Edge) : IsProbabilityMeasure (finiteTreeFrozenCoordinateMeasure G tree edge) := by
    unfold finiteTreeFrozenCoordinateMeasure
    split <;> infer_instance
  simp [finiteTreeFrozenProductMeasure]

/-- Every coordinate marginal is exactly its frozen-or-Haar factor. -/
theorem finiteTreeFrozenProductMeasure_map_eval
    (Edge : Type uEdge) [Fintype Edge] [DecidableEq Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tree : Finset Edge) (edge : Edge) :
    Measure.map (Function.eval edge) (finiteTreeFrozenProductMeasure Edge G tree) =
      finiteTreeFrozenCoordinateMeasure G tree edge := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  letI (index : Edge) : IsProbabilityMeasure (finiteTreeFrozenCoordinateMeasure G tree index) := by
    unfold finiteTreeFrozenCoordinateMeasure
    split <;> infer_instance
  exact (measurePreserving_eval (finiteTreeFrozenCoordinateMeasure G tree) edge).map_eq

end

end YangMills.Mathematics
