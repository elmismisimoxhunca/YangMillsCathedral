/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.GradedLieBracketWedge

/-!
# Graded bracket wedges on tuples with vertical slots

For a horizontal finite-arity form, a one-form bracket wedge evaluated on a tuple with one argument
in the kernel of a linear projection reduces to the single omitted-slot term. With two distinct
kernel arguments it vanishes.
-/

namespace YangMills.Mathematics

universe uQ uT uV

noncomputable section

variable
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousLieBracket V]
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]
    {Q : Type uQ} [AddCommGroup Q] [Module ℝ Q]

/-- On a tuple whose `r`-th entry is vertical, bracketing a one-form with a horizontal
`n`-form leaves exactly the `r`-th omitted-slot summand. -/
theorem ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_verticalSlot
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (projection : T →ₗ[ℝ] Q)
    (horizontal : ∀ args : Fin n → T,
      (∃ i, projection (args i) = 0) → beta args = 0)
    (v : Fin (n + 1) → T) (r : Fin (n + 1))
    (vertical : projection (v r) = 0) :
    alpha.lieBracketWedgeOneMany n beta v =
      (-1 : ℤ) ^ (r : ℕ) • ⁅alpha (fun _ => v r), beta (r.removeNth v)⁆ := by
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply]
  apply Finset.sum_eq_single r
  · intro i hi hir
    have beta_zero : beta (i.removeNth v) = 0 := by
      apply horizontal
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hir.symm
      refine ⟨j, ?_⟩
      rw [Fin.removeNth_apply, hj, vertical]
    rw [beta_zero, lie_zero, smul_zero]
  · simp


/-- A bracket correction built from a horizontal form vanishes on tuples with two distinct
vertical slots. Thus it has the expected two-vertical-slot tensoriality even though it need not be
horizontal on a tuple with only one vertical slot. -/
theorem ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_twoVerticalSlots
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (projection : T →ₗ[ℝ] Q)
    (horizontal : ∀ args : Fin n → T,
      (∃ i, projection (args i) = 0) → beta args = 0)
    (v : Fin (n + 1) → T) (r s : Fin (n + 1)) (hrs : r ≠ s)
    (vertical_r : projection (v r) = 0) (vertical_s : projection (v s) = 0) :
    alpha.lieBracketWedgeOneMany n beta v = 0 := by
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_verticalSlot
    n alpha beta projection horizontal v r vertical_r]
  have beta_zero : beta (r.removeNth v) = 0 := by
    apply horizontal
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hrs.symm
    refine ⟨j, ?_⟩
    rw [Fin.removeNth_apply, hj, vertical_s]
  rw [beta_zero, lie_zero, smul_zero]

end

end YangMills.Mathematics
