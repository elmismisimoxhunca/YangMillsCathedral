/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeWord
import Mathlib.Data.List.Chain

/-!
# Endpoint gauge transport of finite oriented-edge words

A finite directed graph stores source and target vertices for each underlying edge. The exact
vertex-gauge action is target-left and source-right-inverse. This module proves that reverse edge
orientation transforms with the reversed endpoints, that a composable word transforms only at its
two outer endpoints, and that a closed composable word transforms by conjugation at its starting
vertex.

These are finite combinatorial/algebraic statements. They do not assert that a word is embedded,
simple, planar, or the boundary of a complementary face.
-/

namespace YangMills.Mathematics

universe uVertex uEdge uG

namespace OrientedEdge

variable {Vertex : Type uVertex} {Edge : Type uEdge}

/-- Source vertex after accounting for the selected orientation. -/
def source (edgeSource edgeTarget : Edge → Vertex) : OrientedEdge Edge → Vertex
  | .forward edge => edgeSource edge
  | .reverse edge => edgeTarget edge

/-- Target vertex after accounting for the selected orientation. -/
def target (edgeSource edgeTarget : Edge → Vertex) : OrientedEdge Edge → Vertex
  | .forward edge => edgeTarget edge
  | .reverse edge => edgeSource edge

@[simp]
theorem source_flip (edgeSource edgeTarget : Edge → Vertex) (edge : OrientedEdge Edge) :
    source edgeSource edgeTarget (flip edge) = target edgeSource edgeTarget edge := by
  cases edge <;> rfl

@[simp]
theorem target_flip (edgeSource edgeTarget : Edge → Vertex) (edge : OrientedEdge Edge) :
    target edgeSource edgeTarget (flip edge) = source edgeSource edgeTarget edge := by
  cases edge <;> rfl

end OrientedEdge

variable
    {Vertex : Type uVertex} {Edge : Type uEdge} {G : Type uG} [Group G]

/-- Target-left, source-right-inverse vertex-gauge action on one stored edge coordinate. -/
def finiteEdgeGaugeAction
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (edge : Edge) : G :=
  gauge (edgeTarget edge) * configuration edge * (gauge (edgeSource edge))⁻¹

/-- Evaluation of either orientation obeys the exact endpoint gauge law. The reverse case uses the
same stored coordinate and swaps endpoints through group inversion. -/
@[simp]
theorem orientedEdge_eval_finiteEdgeGaugeAction
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (edge : OrientedEdge Edge) :
    OrientedEdge.eval (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration) edge =
      gauge (OrientedEdge.target edgeSource edgeTarget edge) *
        OrientedEdge.eval configuration edge *
          (gauge (OrientedEdge.source edgeSource edgeTarget edge))⁻¹ := by
  cases edge with
  | forward edge => rfl
  | reverse edge =>
      simp [finiteEdgeGaugeAction, OrientedEdge.eval,
        OrientedEdge.source, OrientedEdge.target]
      group

/-- Adjacent oriented edges are composable exactly when the first target is the second source. -/
def OrientedEdgeComposable
    (edgeSource edgeTarget : Edge → Vertex)
    (first second : OrientedEdge Edge) : Prop :=
  OrientedEdge.target edgeSource edgeTarget first =
    OrientedEdge.source edgeSource edgeTarget second

/-- A nonempty composable finite word transforms only at its final target and initial source. -/
theorem finiteOrientedWordHolonomy_gauge_of_chain
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G)
    (configuration : Edge → G) (first : OrientedEdge Edge)
    (tail : List (OrientedEdge Edge))
    (chain : List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) (first :: tail)) :
    finiteOrientedWordHolonomy
        (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration) (first :: tail) =
      gauge (OrientedEdge.target edgeSource edgeTarget
          ((first :: tail).getLast (by simp))) *
        finiteOrientedWordHolonomy configuration (first :: tail) *
          (gauge (OrientedEdge.source edgeSource edgeTarget first))⁻¹ := by
  induction tail generalizing first with
  | nil =>
      simp only [finiteOrientedWordHolonomy_cons, finiteOrientedWordHolonomy_nil,
        one_mul, List.getLast_singleton]
      exact orientedEdge_eval_finiteEdgeGaugeAction
        edgeSource edgeTarget gauge configuration first
  | cons next rest ih =>
      have adjacent : OrientedEdgeComposable edgeSource edgeTarget first next :=
        (List.isChain_cons_cons.mp chain).1
      have restChain :
          List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) (next :: rest) :=
        (List.isChain_cons_cons.mp chain).2
      calc
        finiteOrientedWordHolonomy
            (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration)
            (first :: next :: rest) =
          finiteOrientedWordHolonomy
              (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration)
              (next :: rest) *
            OrientedEdge.eval
              (finiteEdgeGaugeAction edgeSource edgeTarget gauge configuration) first := rfl
        _ = (gauge (OrientedEdge.target edgeSource edgeTarget
                ((next :: rest).getLast (by simp))) *
              finiteOrientedWordHolonomy configuration (next :: rest) *
              (gauge (OrientedEdge.source edgeSource edgeTarget next))⁻¹) *
            (gauge (OrientedEdge.target edgeSource edgeTarget first) *
              OrientedEdge.eval configuration first *
              (gauge (OrientedEdge.source edgeSource edgeTarget first))⁻¹) := by
          rw [ih next restChain, orientedEdge_eval_finiteEdgeGaugeAction]
        _ = gauge (OrientedEdge.target edgeSource edgeTarget
                ((first :: next :: rest).getLast (by simp))) *
              finiteOrientedWordHolonomy configuration (first :: next :: rest) *
              (gauge (OrientedEdge.source edgeSource edgeTarget first))⁻¹ := by
          rw [List.getLast_cons_cons]
          unfold OrientedEdgeComposable at adjacent
          rw [adjacent]
          simp only [finiteOrientedWordHolonomy_cons]
          group

/-- Closing the final target at the initial source specializes endpoint covariance to conjugation
at the exact starting vertex. -/
theorem finiteOrientedWordHolonomy_gauge_of_closed_chain
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
          (gauge (OrientedEdge.source edgeSource edgeTarget first))⁻¹ := by
  rw [finiteOrientedWordHolonomy_gauge_of_chain
    edgeSource edgeTarget gauge configuration first tail chain, closed]

end YangMills.Mathematics
