/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group

/-!
# Finite oriented-edge words

A finite graph configuration stores one group value for each unoriented/positive edge. Traversing an
edge backwards uses the inverse of that same value rather than a second independent coordinate.
For a word traversed in list order, the total transport multiplies later edges on the left. Thus
`wordHolonomy (p ++ q) = wordHolonomy q * wordHolonomy p`, matching the path convention used by the
project's Driver-facing holonomy layer.

This module is purely finite algebra. It supplies no planar embedding, face, area, probability law,
or Yang--Mills object.
-/

namespace YangMills.Mathematics

universe uEdge uG

/-- One orientation of a stored positive/unoriented edge coordinate. -/
inductive OrientedEdge (Edge : Type uEdge) where
  | forward : Edge → OrientedEdge Edge
  | reverse : Edge → OrientedEdge Edge
  deriving DecidableEq

namespace OrientedEdge

variable {Edge : Type uEdge}

/-- Reverse the orientation without changing the underlying stored edge. -/
def flip : OrientedEdge Edge → OrientedEdge Edge
  | forward edge => reverse edge
  | reverse edge => forward edge

@[simp]
theorem flip_forward (edge : Edge) : flip (forward edge) = reverse edge :=
  rfl

@[simp]
theorem flip_reverse (edge : Edge) : flip (reverse edge) = forward edge :=
  rfl

@[simp]
theorem flip_flip (edge : OrientedEdge Edge) : flip (flip edge) = edge := by
  cases edge <;> rfl

/-- Evaluate an oriented edge using one exact group coordinate per underlying edge. -/
def eval {G : Type uG} [Group G] (configuration : Edge → G) : OrientedEdge Edge → G
  | forward edge => configuration edge
  | reverse edge => (configuration edge)⁻¹

@[simp]
theorem eval_forward {G : Type uG} [Group G]
    (configuration : Edge → G) (edge : Edge) :
    eval configuration (forward edge) = configuration edge :=
  rfl

@[simp]
theorem eval_reverse {G : Type uG} [Group G]
    (configuration : Edge → G) (edge : Edge) :
    eval configuration (reverse edge) = (configuration edge)⁻¹ :=
  rfl

@[simp]
theorem eval_flip {G : Type uG} [Group G]
    (configuration : Edge → G) (edge : OrientedEdge Edge) :
    eval configuration (flip edge) = (eval configuration edge)⁻¹ := by
  cases edge <;> simp [eval, flip]

end OrientedEdge

/-- Transport along a finite oriented word, traversed in list order. Later edge transports multiply
on the left, exactly as for the project's `concat` path convention. -/
def finiteOrientedWordHolonomy
    {Edge : Type uEdge} {G : Type uG} [Group G]
    (configuration : Edge → G) : List (OrientedEdge Edge) → G
  | [] => 1
  | edge :: tail => finiteOrientedWordHolonomy configuration tail *
      OrientedEdge.eval configuration edge

@[simp]
theorem finiteOrientedWordHolonomy_nil
    {Edge : Type uEdge} {G : Type uG} [Group G] (configuration : Edge → G) :
    finiteOrientedWordHolonomy configuration [] = 1 :=
  rfl

@[simp]
theorem finiteOrientedWordHolonomy_cons
    {Edge : Type uEdge} {G : Type uG} [Group G]
    (configuration : Edge → G) (edge : OrientedEdge Edge)
    (tail : List (OrientedEdge Edge)) :
    finiteOrientedWordHolonomy configuration (edge :: tail) =
      finiteOrientedWordHolonomy configuration tail * OrientedEdge.eval configuration edge :=
  rfl

/-- Concatenating words means traversing the first and then the second, hence the second total
transport multiplies on the left. -/
theorem finiteOrientedWordHolonomy_append
    {Edge : Type uEdge} {G : Type uG} [Group G]
    (configuration : Edge → G) (first second : List (OrientedEdge Edge)) :
    finiteOrientedWordHolonomy configuration (first ++ second) =
      finiteOrientedWordHolonomy configuration second *
        finiteOrientedWordHolonomy configuration first := by
  induction first with
  | nil => simp
  | cons edge tail ih =>
      simp only [List.cons_append, finiteOrientedWordHolonomy_cons, ih]
      simp [mul_assoc]

/-- Reverse traversal reverses list order and flips every edge orientation. -/
def reverseFiniteOrientedWord {Edge : Type uEdge}
    (word : List (OrientedEdge Edge)) : List (OrientedEdge Edge) :=
  word.reverse.map OrientedEdge.flip

@[simp]
theorem reverseFiniteOrientedWord_nil {Edge : Type uEdge} :
    reverseFiniteOrientedWord ([] : List (OrientedEdge Edge)) = [] :=
  rfl

/-- Reversing a finite word twice recovers the exact original word. -/
@[simp]
theorem reverseFiniteOrientedWord_reverseFiniteOrientedWord
    {Edge : Type uEdge} (word : List (OrientedEdge Edge)) :
    reverseFiniteOrientedWord (reverseFiniteOrientedWord word) = word := by
  simp [reverseFiniteOrientedWord, List.map_reverse, Function.comp_def]

/-- Exact inversion law for reverse traversal of a finite oriented word. -/
@[simp]
theorem finiteOrientedWordHolonomy_reverse
    {Edge : Type uEdge} {G : Type uG} [Group G]
    (configuration : Edge → G) (word : List (OrientedEdge Edge)) :
    finiteOrientedWordHolonomy configuration (reverseFiniteOrientedWord word) =
      (finiteOrientedWordHolonomy configuration word)⁻¹ := by
  induction word with
  | nil => simp
  | cons edge tail ih =>
      rw [show reverseFiniteOrientedWord (edge :: tail) =
        reverseFiniteOrientedWord tail ++ [OrientedEdge.flip edge] by
          simp [reverseFiniteOrientedWord, List.map_reverse]]
      rw [finiteOrientedWordHolonomy_append, ih]
      simp [mul_inv_rev]

end YangMills.Mathematics
