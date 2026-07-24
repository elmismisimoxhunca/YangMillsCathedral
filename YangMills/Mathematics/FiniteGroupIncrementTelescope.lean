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

/-- Ordered prefix products of a finite increment vector. Coordinate `i` multiplies entries
`0,…,i` in that order. -/
def finiteRightIncrementPrefixProducts
    {G : Type*} [Group G] (n : ℕ) (increment : Fin n → G) (i : Fin n) : G :=
  (List.ofFn (fun j : Fin (i.val + 1) =>
    increment ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) i.isLt⟩)).prod

/-- Every prefix of the consecutive right-increment vector telescopes to its corresponding
endpoint. -/
theorem finiteRightIncrementPrefixProducts_eq_endpoints
    {G : Type*} [Group G] (n : ℕ) (value : Fin (n + 1) → G) (i : Fin n) :
    finiteRightIncrementPrefixProducts n
        (fun k => (value k.castSucc)⁻¹ * value k.succ) i =
      (value 0)⁻¹ * value i.succ := by
  unfold finiteRightIncrementPrefixProducts
  let prefixValue : Fin (i.val + 2) → G := fun j =>
    value ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt)
      (Nat.add_lt_add_right i.isLt 1)⟩
  have telescope := finiteRightIncrementProduct_eq_endpoints (i.val + 1) prefixValue
  convert telescope using 1 <;> simp [prefixValue]
  apply congrArg value
  exact Fin.ext rfl

end YangMills.Mathematics
