/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteGroupIncrementTelescope

/-!
# Hostile probes for finite group increment telescoping
-/

namespace YangMills.Mathematics

/-- Two consecutive right increments telescope in the stated noncommutative order. -/
theorem two_right_increments_exact
    {G : Type*} [Group G] (value : Fin 3 → G) :
    ((value 0)⁻¹ * value 1) * ((value 1)⁻¹ * value 2) =
      (value 0)⁻¹ * value 2 := by
  group

/-- The zero-increment endpoint formula is the identity, not an empty-endpoint surrogate. -/
theorem zero_right_increments_exact
    {G : Type*} [Group G] (value : Fin 1 → G) :
    (List.ofFn (fun i : Fin 0 => (value i.castSucc)⁻¹ * value i.succ)).prod = 1 := by
  simp

/-- Every first-coordinate prefix is the first right increment. -/
theorem first_right_increment_prefix_exact
    {G : Type*} [Group G] (n : ℕ) (value : Fin (n + 2) → G) :
    finiteRightIncrementPrefixProducts (n + 1)
        (fun k => (value k.castSucc)⁻¹ * value k.succ) 0 =
      (value 0)⁻¹ * value 1 :=
  finiteRightIncrementPrefixProducts_eq_endpoints (n + 1) value 0

/-- Hostile endpoint probe: replacing the exact endpoint expression by a distinct value contradicts
the telescoping theorem. -/
theorem changed_right_increment_endpoint_blocked
    {G : Type*} [Group G] (n : ℕ) (value : Fin (n + 1) → G) (changed : G)
    (changed_ne_exact : changed ≠ (value 0)⁻¹ * value (Fin.last n))
    (claimed :
      (List.ofFn (fun i : Fin n => (value i.castSucc)⁻¹ * value i.succ)).prod = changed) : False := by
  rw [finiteRightIncrementProduct_eq_endpoints] at claimed
  exact changed_ne_exact claimed.symm

end YangMills.Mathematics
