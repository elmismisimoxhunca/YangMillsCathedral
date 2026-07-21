/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeWord

/-!
# Probes for finite oriented-edge words

These probes pin one coordinate per underlying edge, inversion under orientation reversal, and the
Driver-compatible later-on-the-left concatenation convention.
-/

namespace YangMills.Mathematics.FiniteOrientedEdgeWord.Probes

universe uEdge uG

variable {Edge : Type uEdge} {G : Type uG} [Group G]

/-- Reversal never introduces a second underlying edge coordinate. -/
theorem exact_underlying_edge_preserved (edge : OrientedEdge Edge) :
    OrientedEdge.underlying (OrientedEdge.flip edge) = OrientedEdge.underlying edge :=
  OrientedEdge.underlying_flip edge

/-- Reverse orientation evaluates by inversion of the same stored edge coordinate. -/
theorem exact_reverse_coordinate (configuration : Edge → G) (edge : Edge) :
    OrientedEdge.eval configuration (.reverse edge) = (configuration edge)⁻¹ :=
  rfl

/-- Traversing `first` and then `second` multiplies the second holonomy on the left. -/
theorem exact_driver_append_order
    (configuration : Edge → G)
    (first second : List (OrientedEdge Edge)) :
    finiteOrientedWordHolonomy configuration (first ++ second) =
      finiteOrientedWordHolonomy configuration second *
        finiteOrientedWordHolonomy configuration first :=
  finiteOrientedWordHolonomy_append configuration first second

/-- Reverse traversal gives the exact inverse group element. -/
theorem exact_reverse_holonomy
    (configuration : Edge → G) (word : List (OrientedEdge Edge)) :
    finiteOrientedWordHolonomy configuration (reverseFiniteOrientedWord word) =
      (finiteOrientedWordHolonomy configuration word)⁻¹ :=
  finiteOrientedWordHolonomy_reverse configuration word

/-- A wrong first-on-the-left multiplication convention is rejected whenever distinguishable. -/
theorem wrong_append_order_blocked
    (configuration : Edge → G)
    (first second : List (OrientedEdge Edge))
    (different :
      finiteOrientedWordHolonomy configuration first *
          finiteOrientedWordHolonomy configuration second ≠
        finiteOrientedWordHolonomy configuration second *
          finiteOrientedWordHolonomy configuration first)
    (claimed : finiteOrientedWordHolonomy configuration (first ++ second) =
      finiteOrientedWordHolonomy configuration first *
        finiteOrientedWordHolonomy configuration second) : False := by
  apply different
  rw [← claimed]
  exact finiteOrientedWordHolonomy_append configuration first second

end YangMills.Mathematics.FiniteOrientedEdgeWord.Probes
