/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteConfigurationSchwartzTensor

/-!
# Hostile probes for finite-configuration Schwartz tensors

The probes lock block indices, unit arity, coordinate order, and exact pure-product evaluation.
They are signature-neutral and construct no Euclidean or Minkowski physical datum.
-/

open scoped SchwartzMap

namespace YangMills.Mathematics.FiniteConfigurationSchwartzTensor.Probes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first block uses the exact unshifted coordinate embedding. -/
theorem exact_left_block
    (n m : ℕ) (x : FiniteConfiguration E (n + m)) (i : Fin n) :
    (finiteConfigurationSplit E n m x).1 i = x (Fin.castAdd m i) :=
  finiteConfigurationSplit_left_apply E n m x i

/-- The second block uses the exact offset coordinate embedding. -/
theorem exact_right_block
    (n m : ℕ) (x : FiniteConfiguration E (n + m)) (j : Fin m) :
    (finiteConfigurationSplit E n m x).2 j = x (Fin.natAdd n j) :=
  finiteConfigurationSplit_right_apply E n m x j

/-- Split and merge are exact inverses. -/
theorem exact_split_merge
    (n m : ℕ) (x : FiniteConfiguration E n) (y : FiniteConfiguration E m) :
    finiteConfigurationSplit E n m (finiteConfigurationMerge E n m (x, y)) = (x, y) :=
  (finiteConfigurationSplit E n m).apply_symm_apply (x, y)

/-- Concatenated tensors evaluate on their exact blocks. -/
theorem exact_concatenated_tensor
    {n m : ℕ} (f : 𝓢(FiniteConfiguration E n, ℂ))
    (g : 𝓢(FiniteConfiguration E m, ℂ))
    (x : FiniteConfiguration E (n + m)) :
    scalarSchwartzTensorProductOnFiniteConfiguration E f g x =
      f (finiteConfigurationSplit E n m x).1 *
        g (finiteConfigurationSplit E n m x).2 :=
  scalarSchwartzTensorProductOnFiniteConfiguration_apply E f g x

/-- The empty pure tensor is exactly one at its unique configuration. -/
theorem empty_pure_tensor_exact
    (f : Fin 0 → 𝓢(E, ℂ)) (x : FiniteConfiguration E 0) :
    scalarSchwartzPureTensor E 0 f x = 1 := by
  rw [scalarSchwartzPureTensor_apply]
  simp

/-- Every finite pure tensor preserves exact coordinate order. -/
theorem exact_pure_tensor_product
    (n : ℕ) (f : Fin n → 𝓢(E, ℂ)) (x : FiniteConfiguration E n) :
    scalarSchwartzPureTensor E n f x = ∏ i, f i (x i) :=
  scalarSchwartzPureTensor_apply E n f x

/-- An unrelated replacement value is rejected against the exact coordinate product. -/
theorem unrelated_pure_tensor_value_blocked
    (n : ℕ) (f : Fin n → 𝓢(E, ℂ)) (x : FiniteConfiguration E n) (z : ℂ)
    (hmismatch : z ≠ ∏ i, f i (x i)) :
    scalarSchwartzPureTensor E n f x ≠ z := by
  rw [scalarSchwartzPureTensor_apply]
  exact fun h => hmismatch h.symm

end YangMills.Mathematics.FiniteConfigurationSchwartzTensor.Probes
