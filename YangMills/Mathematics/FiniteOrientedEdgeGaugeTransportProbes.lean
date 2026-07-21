/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeGaugeTransport

/-!
# Probes for finite oriented-edge gauge transport

These probes retain oriented endpoints, target-left edge covariance, cancellation at every internal
vertex of a composable word, and conjugation of a closed word at its exact starting vertex.
-/

namespace YangMills.Mathematics.FiniteOrientedEdgeGaugeTransport.Probes

universe uVertex uEdge uG

variable
    {Vertex : Type uVertex} {Edge : Type uEdge} {G : Type uG} [Group G]

/-- Flipping orientation swaps the exact source and target. -/
theorem exact_flipped_endpoints
    (edgeSource edgeTarget : Edge → Vertex) (edge : OrientedEdge Edge) :
    OrientedEdge.source edgeSource edgeTarget (OrientedEdge.flip edge) =
      OrientedEdge.target edgeSource edgeTarget edge ∧
    OrientedEdge.target edgeSource edgeTarget (OrientedEdge.flip edge) =
      OrientedEdge.source edgeSource edgeTarget edge := by
  simp

/-- Reverse orientation derives its covariance from the same stored coordinate. -/
theorem exact_reverse_edge_covariance
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (edge : Edge) :
    OrientedEdge.eval
        (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration)
        (.reverse edge) =
      gauge (edgeSource edge) * (configuration edge)⁻¹ *
        (gauge (edgeTarget edge))⁻¹ :=
  orientedEdge_eval_finiteEdgeGaugeAction
    edgeSource edgeTarget gauge configuration (.reverse edge)

/-- A composable word has only its final-target and initial-source gauge factors. -/
theorem exact_open_word_endpoint_covariance
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (first : OrientedEdge Edge)
    (tail : List (OrientedEdge Edge))
    (chain : List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) (first :: tail)) :
    finiteOrientedWordHolonomy
        (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration) (first :: tail) =
      gauge (OrientedEdge.target edgeSource edgeTarget
          ((first :: tail).getLast (by simp))) *
        finiteOrientedWordHolonomy configuration (first :: tail) *
          (gauge (OrientedEdge.source edgeSource edgeTarget first))⁻¹ :=
  finiteOrientedWordHolonomy_gauge_of_chain
    edgeSource edgeTarget gauge configuration first tail chain

/-- A closed composable word transforms by exact conjugation at its starting vertex. -/
theorem exact_closed_word_conjugation
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (first : OrientedEdge Edge)
    (tail : List (OrientedEdge Edge))
    (chain : List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) (first :: tail))
    (closed : OrientedEdge.target edgeSource edgeTarget
        ((first :: tail).getLast (by simp)) =
      OrientedEdge.source edgeSource edgeTarget first) :
    finiteOrientedWordHolonomy
        (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration) (first :: tail) =
      gauge (OrientedEdge.source edgeSource edgeTarget first) *
        finiteOrientedWordHolonomy configuration (first :: tail) *
          (gauge (OrientedEdge.source edgeSource edgeTarget first))⁻¹ :=
  finiteOrientedWordHolonomy_gauge_of_closed_chain
    edgeSource edgeTarget gauge configuration first tail chain closed

/-- A wrong source-left/target-right endpoint law is rejected whenever distinguishable. -/
theorem wrong_endpoint_orientation_blocked
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (edge : OrientedEdge Edge)
    (different :
      gauge (OrientedEdge.source edgeSource edgeTarget edge) *
          OrientedEdge.eval configuration edge *
          (gauge (OrientedEdge.target edgeSource edgeTarget edge))⁻¹ ≠
        gauge (OrientedEdge.target edgeSource edgeTarget edge) *
          OrientedEdge.eval configuration edge *
          (gauge (OrientedEdge.source edgeSource edgeTarget edge))⁻¹)
    (claimed :
      OrientedEdge.eval
          (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration) edge =
        gauge (OrientedEdge.source edgeSource edgeTarget edge) *
          OrientedEdge.eval configuration edge *
          (gauge (OrientedEdge.target edgeSource edgeTarget edge))⁻¹) : False := by
  apply different
  rw [← claimed]
  exact orientedEdge_eval_finiteEdgeGaugeAction
    edgeSource edgeTarget gauge configuration edge

end YangMills.Mathematics.FiniteOrientedEdgeGaugeTransport.Probes
