/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteBoundaryConnectedWord

/-!
# Probes for finite BC boundary words

These probes distinguish legitimate opposite-orientation bridge multiplicity from doubled traversal
of a cycle edge, and expose nonempty, composable, and closed boundary requirements.
-/

namespace YangMills.Mathematics.FiniteBoundaryConnectedWord.Probes

universe uVertex uEdge

variable
    {Vertex : Type uVertex} {Edge : Type uEdge} [DecidableEq Edge]
    {edgeSource edgeTarget : Edge → Vertex} {word : List (OrientedEdge Edge)}

omit [DecidableEq Edge] in
/-- Bridge status is exactly absence of an avoiding source-to-target word. -/
theorem exact_bridge_semantics (edge : Edge) :
    FiniteGraphEdgeIsBridge edgeSource edgeTarget edge ↔
      ¬ ∃ alternative : List (OrientedEdge Edge),
        OrientedEdgeWordRunsFrom edgeSource edgeTarget alternative
          (edgeSource edge) (edgeTarget edge) ∧
        ∀ oriented ∈ alternative, OrientedEdge.underlying oriented ≠ edge :=
  Iff.rfl

omit [DecidableEq Edge] in
/-- A loop edge is not falsely classified as a bridge: the empty alternative path remains after
removing it. -/
theorem loop_edge_not_bridge (edge : Edge)
    (loop : edgeSource edge = edgeTarget edge) :
    ¬ FiniteGraphEdgeIsBridge edgeSource edgeTarget edge := by
  intro bridge
  apply bridge
  refine ⟨[], ?_, ?_⟩
  · exact Or.inl ⟨rfl, loop⟩
  · intro oriented membership
    simp at membership

omit [DecidableEq Edge] in
/-- A distinct parallel edge is an explicit avoiding path, so neither parallel edge is a bridge. -/
theorem parallel_edge_not_bridge (edge other : Edge) (different : other ≠ edge)
    (same_source : edgeSource other = edgeSource edge)
    (same_target : edgeTarget other = edgeTarget edge) :
    ¬ FiniteGraphEdgeIsBridge edgeSource edgeTarget edge := by
  intro bridge
  apply bridge
  refine ⟨[.forward other], ?_, ?_⟩
  · refine Or.inr ⟨by simp, by simp, ?_, ?_⟩
    · change edgeSource other = edgeSource edge
      exact same_source
    · change edgeTarget other = edgeTarget edge
      exact same_target
  · intro oriented membership
    simp only [List.mem_singleton] at membership
    subst oriented
    simpa using different

/-- A legitimate boundary bridge has equal forward and reverse multiplicity, each at most one. -/
theorem exact_bridge_multiplicity
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge) (bridge : FiniteGraphEdgeIsBridge edgeSource edgeTarget edge) :
    word.count (.forward edge) = word.count (.reverse edge) ∧
      word.count (.forward edge) ≤ 1 ∧ word.count (.reverse edge) ≤ 1 :=
  ⟨BoundaryConnectedWordCertificate.bridge_forward_count_eq_reverse_count certificate edge bridge,
    BoundaryConnectedWordCertificate.bridge_forward_le_one certificate edge bridge,
    BoundaryConnectedWordCertificate.bridge_reverse_count_le_one certificate edge bridge⟩

/-- A nonbridge underlying edge can occur at most once total. -/
theorem exact_nonbridge_multiplicity
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge) (not_bridge : ¬ FiniteGraphEdgeIsBridge edgeSource edgeTarget edge) :
    word.count (.forward edge) + word.count (.reverse edge) ≤ 1 :=
  BoundaryConnectedWordCertificate.nonbridge_total_count_le_one certificate edge not_bridge

/-- Any doubled underlying-edge traversal must carry an actual bridge proof. -/
theorem arbitrary_doubling_blocked
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge)
    (repeated : 2 ≤ word.count (.forward edge) + word.count (.reverse edge)) :
    FiniteGraphEdgeIsBridge edgeSource edgeTarget edge :=
  BoundaryConnectedWordCertificate.repeated_underlying_edge_is_bridge certificate edge repeated

/-- A doubled circuit edge is rejected when the rest of the circuit supplies an avoiding path. -/
theorem doubled_cycle_edge_blocked
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge)
    (alternative : ∃ path : List (OrientedEdge Edge),
      OrientedEdgeWordRunsFrom edgeSource edgeTarget path
        (edgeSource edge) (edgeTarget edge) ∧
      ∀ oriented ∈ path, OrientedEdge.underlying oriented ≠ edge)
    (repeated : 2 ≤ word.count (.forward edge) + word.count (.reverse edge)) : False := by
  have not_bridge : ¬ FiniteGraphEdgeIsBridge edgeSource edgeTarget edge := by
    intro bridge
    exact bridge alternative
  exact not_bridge
    (BoundaryConnectedWordCertificate.repeated_underlying_edge_is_bridge certificate edge repeated)

/-- A proposed bridge with unequal orientation counts cannot carry the certificate. -/
theorem one_sided_bridge_repetition_blocked
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (edge : Edge) (bridge : FiniteGraphEdgeIsBridge edgeSource edgeTarget edge)
    (unequal : word.count (.forward edge) ≠ word.count (.reverse edge)) : False :=
  unequal
    (BoundaryConnectedWordCertificate.bridge_forward_count_eq_reverse_count certificate edge bridge)

/-- Empty words are excluded. -/
theorem empty_boundary_blocked
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word)
    (claimed : word = []) : False :=
  (BoundaryConnectedWordCertificate.nonempty certificate) claimed

/-- Every adjacent pair in the exact boundary word is endpoint-composable. -/
theorem exact_boundary_chain
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word) :
    List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) word :=
  BoundaryConnectedWordCertificate.chain certificate

/-- The exact terminal and initial vertices of every admitted word agree. -/
theorem exact_closed_boundary
    (certificate : BoundaryConnectedWordCertificate edgeSource edgeTarget word) :
    OrientedEdge.target edgeSource edgeTarget (word.getLast (BoundaryConnectedWordCertificate.nonempty certificate)) =
      OrientedEdge.source edgeSource edgeTarget (word.head (BoundaryConnectedWordCertificate.nonempty certificate)) :=
  BoundaryConnectedWordCertificate.closed certificate

end YangMills.Mathematics.FiniteBoundaryConnectedWord.Probes
