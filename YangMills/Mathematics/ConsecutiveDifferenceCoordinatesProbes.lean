/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ConsecutiveDifferenceCoordinates

/-!
# Hostile probes for consecutive-difference coordinates

The probes lock difference signs, final-anchor choice, inverse reconstruction, common-translation
behavior, and exact Schwartz lifting. No physical translation-invariance claim is made.
-/

namespace YangMills.Mathematics.ConsecutiveDifferenceCoordinates.Probes

open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The relative block uses exact consecutive differences `xᵢ - xᵢ₊₁`. -/
theorem exact_consecutive_difference
    (n : ℕ) (x : Fin (n + 1) → E) (i : Fin n) :
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n x).1 i =
      x i.castSucc - x i.succ :=
  consecutiveDifferenceAnchorContinuousLinearEquiv_fst_apply E n x i

/-- The distinguished anchor is exactly the final point. -/
theorem exact_final_anchor
    (n : ℕ) (x : Fin (n + 1) → E) :
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n x).2 = x (Fin.last n) :=
  consecutiveDifferenceAnchorContinuousLinearEquiv_snd_apply E n x

/-- Reconstruction is the exact inverse of difference/anchor extraction. -/
theorem exact_reconstruction
    (n : ℕ) (ξ : Fin n → E) (anchor : E) :
    consecutiveDifferenceAnchorContinuousLinearEquiv E n
      ((consecutiveDifferenceAnchorContinuousLinearEquiv E n).symm (ξ, anchor)) =
      (ξ, anchor) :=
  (consecutiveDifferenceAnchorContinuousLinearEquiv E n).apply_symm_apply (ξ, anchor)

/-- A common translation leaves every consecutive difference unchanged. -/
theorem common_translation_preserves_differences
    (n : ℕ) (x : Fin (n + 1) → E) (a : E) :
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n (fun i => x i + a)).1 =
      (consecutiveDifferenceAnchorContinuousLinearEquiv E n x).1 := by
  funext i
  simp

/-- The same common translation moves the final anchor by exactly `a`. -/
theorem common_translation_moves_anchor
    (n : ℕ) (x : Fin (n + 1) → E) (a : E) :
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n (fun i => x i + a)).2 =
      (consecutiveDifferenceAnchorContinuousLinearEquiv E n x).2 + a :=
  rfl

/-- Relative/anchor Schwartz lifting has the exact source-facing product kernel. -/
theorem exact_relative_anchor_lift
    {n : ℕ} (relative : 𝓢(Fin n → E, ℂ)) (anchor : 𝓢(E, ℂ))
    (x : Fin (n + 1) → E) :
    relativeAnchorSchwartzLift E relative anchor x =
      relative (fun i => x i.castSucc - x i.succ) * anchor (x (Fin.last n)) :=
  relativeAnchorSchwartzLift_apply E relative anchor x

/-- An unrelated replacement value is blocked by exact relative/anchor evaluation. -/
theorem unrelated_relative_anchor_value_blocked
    {n : ℕ} (relative : 𝓢(Fin n → E, ℂ)) (anchor : 𝓢(E, ℂ))
    (x : Fin (n + 1) → E) (z : ℂ)
    (hmismatch : z ≠
      relative (fun i => x i.castSucc - x i.succ) * anchor (x (Fin.last n))) :
    relativeAnchorSchwartzLift E relative anchor x ≠ z := by
  rw [relativeAnchorSchwartzLift_apply]
  exact fun h => hmismatch h.symm

end YangMills.Mathematics.ConsecutiveDifferenceCoordinates.Probes
