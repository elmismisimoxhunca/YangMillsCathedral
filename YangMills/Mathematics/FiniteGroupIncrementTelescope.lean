/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Group

/-!
# Telescoping products of finite group-valued right increments

For values `x₀,…,xₙ` in an arbitrary group, the ordered product of right increments
`(x₀⁻¹x₁)(x₁⁻¹x₂)…(xₙ₋₁⁻¹xₙ)` is exactly `x₀⁻¹xₙ`. No commutativity is assumed.
-/

namespace YangMills.Mathematics

/-- Ordered noncommutative telescoping of a finite family of right increments. The `List.ofFn`
order is part of the statement and fixes earlier increments on the left. -/
theorem finiteRightIncrementProduct_eq_endpoints
    {G : Type*} [Group G] (n : ℕ) (value : Fin (n + 1) → G) :
    (List.ofFn (fun i : Fin n => (value i.castSucc)⁻¹ * value i.succ)).prod =
      (value 0)⁻¹ * value (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.prod_concat]
      simp_rw [Fin.succ_castSucc]
      rw [ih (fun i : Fin (n + 1) => value i.castSucc)]
      simp only [Fin.castSucc_zero, Fin.succ_last]
      group

end YangMills.Mathematics
