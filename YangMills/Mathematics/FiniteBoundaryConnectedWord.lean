/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeGaugeTransport

/-!
# Finite boundary-connected graph words

This module isolates the finite combinatorics needed for Driver's boundary-connected (BC) graph
scope. An edge is a bridge exactly when there is no composable oriented word from its
source to its target avoiding that underlying edge. A certified BC boundary word may traverse a
bridge once in each orientation, but may use a nonbridge underlying edge at most once total.

This distinction permits legitimate bridge/cut-edge multiplicity while rejecting a doubled circuit
whose repeated edges lie on a cycle. It is finite graph combinatorics only: no planar embedding,
face, density, measure, or Yang--Mills object is constructed here.
-/

namespace YangMills.Mathematics

universe uVertex uEdge

/-- A composable oriented word with prescribed initial and terminal vertices. The empty word runs
from a vertex to itself, ensuring that a loop edge is correctly classified as a nonbridge. -/
def OrientedEdgeWordRunsFrom
    {Vertex : Type uVertex} {Edge : Type uEdge}
    (edgeSource edgeTarget : Edge → Vertex)
    (word : List (OrientedEdge Edge)) (start finish : Vertex) : Prop :=
  (word = [] ∧ start = finish) ∨
    ∃ nonempty : word ≠ [],
      List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) word ∧
        OrientedEdge.source edgeSource edgeTarget (word.head nonempty) = start ∧
        OrientedEdge.target edgeSource edgeTarget (word.getLast nonempty) = finish

/-- Exact combinatorial bridge predicate: after deleting the underlying edge, no oriented use of
the remaining graph joins its source to its target. Orientations remain available in both directions
for every other stored edge. -/
def FiniteGraphEdgeIsBridge
    {Vertex : Type uVertex} {Edge : Type uEdge}
    (edgeSource edgeTarget : Edge → Vertex) (forbidden : Edge) : Prop :=
  ¬ ∃ word : List (OrientedEdge Edge),
    OrientedEdgeWordRunsFrom edgeSource edgeTarget word
      (edgeSource forbidden) (edgeTarget forbidden) ∧
    ∀ oriented ∈ word, OrientedEdge.underlying oriented ≠ forbidden

/-- One closed finite boundary walk with exact BC bridge multiplicities. Bridge edges are absent or
occur once forward and once reverse; every nonbridge underlying edge occurs at most once total. -/
structure BoundaryConnectedWordCertificate
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    (edgeSource edgeTarget : Edge → Vertex) (word : List (OrientedEdge Edge)) where
  nonempty : word ≠ []
  chain : List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) word
  closed :
    OrientedEdge.target edgeSource edgeTarget (word.getLast nonempty) =
      OrientedEdge.source edgeSource edgeTarget (word.head nonempty)
  bridge_forward_eq_reverse : ∀ edge,
    FiniteGraphEdgeIsBridge edgeSource edgeTarget edge →
      word.count (.forward edge) = word.count (.reverse edge)
  bridge_forward_le_one : ∀ edge,
    FiniteGraphEdgeIsBridge edgeSource edgeTarget edge →
      word.count (.forward edge) ≤ 1
  nonbridge_total_le_one : ∀ edge,
    ¬ FiniteGraphEdgeIsBridge edgeSource edgeTarget edge →
      word.count (.forward edge) + word.count (.reverse edge) ≤ 1

namespace BoundaryConnectedWordCertificate

variable
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    {edgeSource edgeTarget : Edge → Vertex} {word : List (OrientedEdge Edge)}

/-- A nonbridge edge can occur at most once in either orientation combined. -/
theorem nonbridge_total_count_le_one
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge) (not_bridge : ¬ FiniteGraphEdgeIsBridge edgeSource edgeTarget edge) :
    word.count (.forward edge) + word.count (.reverse edge) ≤ 1 := by
  exact certificate.nonbridge_total_le_one edge not_bridge

/-- The two orientation counts of a bridge agree. -/
theorem bridge_forward_count_eq_reverse_count
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge) (bridge : FiniteGraphEdgeIsBridge edgeSource edgeTarget edge) :
    word.count (.forward edge) = word.count (.reverse edge) := by
  exact certificate.bridge_forward_eq_reverse edge bridge

/-- Each orientation of a bridge occurs at most once. -/
theorem bridge_reverse_count_le_one
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge) (bridge : FiniteGraphEdgeIsBridge edgeSource edgeTarget edge) :
    word.count (.reverse edge) ≤ 1 := by
  rw [← certificate.bridge_forward_eq_reverse edge bridge]
  exact certificate.bridge_forward_le_one edge bridge

/-- Any repeated underlying edge in a certified boundary is necessarily a bridge. -/
theorem repeated_underlying_edge_is_bridge
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge)
    (repeated : 2 ≤ word.count (.forward edge) + word.count (.reverse edge)) :
    FiniteGraphEdgeIsBridge edgeSource edgeTarget edge := by
  by_contra not_bridge
  have at_most_one := certificate.nonbridge_total_count_le_one edge not_bridge
  omega

end BoundaryConnectedWordCertificate

end YangMills.Mathematics
