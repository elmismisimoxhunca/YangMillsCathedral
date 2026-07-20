/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieBracketWedgeHorizontalVertical

/-!
# Hostile probes for vertical-slot bracket wedges
-/

namespace YangMills.Mathematics.LieBracketWedgeHorizontalVertical.Probes

universe uQ uT uV

variable
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousLieBracket V]
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]
    {Q : Type uQ} [AddCommGroup Q] [Module ℝ Q]

/-- One kernel slot leaves exactly its signed omitted-slot summand. -/
theorem exact_one_vertical_slot
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (projection : T →ₗ[ℝ] Q)
    (horizontal : ∀ args : Fin n → T, (∃ i, projection (args i) = 0) → beta args = 0)
    (v : Fin (n + 1) → T) (r : Fin (n + 1)) (vertical : projection (v r) = 0) :
    alpha.lieBracketWedgeOneMany n beta v =
      (-1 : ℤ) ^ (r : ℕ) • ⁅alpha (fun _ => v r), beta (r.removeNth v)⁆ :=
  YangMills.Mathematics.ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_verticalSlot
    n alpha beta projection horizontal v r vertical

/-- Two distinct kernel slots force the correction to vanish. -/
theorem exact_two_vertical_slots
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (projection : T →ₗ[ℝ] Q)
    (horizontal : ∀ args : Fin n → T, (∃ i, projection (args i) = 0) → beta args = 0)
    (v : Fin (n + 1) → T) (r s : Fin (n + 1)) (hrs : r ≠ s)
    (vertical_r : projection (v r) = 0) (vertical_s : projection (v s) = 0) :
    alpha.lieBracketWedgeOneMany n beta v = 0 :=
  YangMills.Mathematics.ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_twoVerticalSlots
    n alpha beta projection horizontal v r s hrs vertical_r vertical_s

/-- A changed one-slot sign or omitted tuple is rejected. -/
theorem mismatched_vertical_slot_formula_blocked
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (projection : T →ₗ[ℝ] Q)
    (horizontal : ∀ args : Fin n → T, (∃ i, projection (args i) = 0) → beta args = 0)
    (v : Fin (n + 1) → T) (r : Fin (n + 1)) (vertical : projection (v r) = 0)
    (wrong : alpha.lieBracketWedgeOneMany n beta v ≠
      (-1 : ℤ) ^ (r : ℕ) • ⁅alpha (fun _ => v r), beta (r.removeNth v)⁆) : False :=
  wrong (YangMills.Mathematics.ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_verticalSlot
    n alpha beta projection horizontal v r vertical)

end YangMills.Mathematics.LieBracketWedgeHorizontalVertical.Probes
