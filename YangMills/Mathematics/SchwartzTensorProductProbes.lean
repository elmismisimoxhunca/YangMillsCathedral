/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzTensorProduct

/-!
# Hostile probes for scalar Schwartz tensor products

The probes ensure both factors control exact evaluation and that the bundled operation has genuine
bilinear behavior. They do not claim joint continuity.
-/

open scoped SchwartzMap

namespace YangMills.Mathematics.Probes

variable {E D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Zeroing the first factor zeroes the bundled tensor product. -/
@[simp] theorem scalarSchwartzTensorProduct_zero_left (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct (0 : 𝓢(E, ℂ)) g = 0 := by
  ext z
  simp

/-- Zeroing the second factor zeroes the bundled tensor product. -/
@[simp] theorem scalarSchwartzTensorProduct_zero_right (f : 𝓢(E, ℂ)) :
    scalarSchwartzTensorProduct f (0 : 𝓢(D, ℂ)) = 0 := by
  ext z
  simp

/-- Nonzero factor evaluations yield a nonzero tensor evaluation at the same pair. -/
theorem nonzero_factor_evaluations_give_nonzero_tensor
    (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) (x : E) (y : D)
    (hfx : f x ≠ 0) (hgy : g y ≠ 0) :
    scalarSchwartzTensorProduct f g (x, y) ≠ 0 := by
  rw [scalarSchwartzTensorProduct_apply]
  exact mul_ne_zero hfx hgy

/-- Replacing exact tensor evaluation by an unrelated scalar contradicts the pointwise theorem. -/
theorem tensor_evaluation_replacement_blocked
    (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) (z : E × D) (value : ℂ)
    (hmismatch : value ≠ f z.1 * g z.2)
    (hreplaced : scalarSchwartzTensorProduct f g z = value) : False := by
  rw [scalarSchwartzTensorProduct_apply] at hreplaced
  exact hmismatch hreplaced.symm

/-- The exact left-additivity law cannot be replaced by a nonlinear first-factor operation. -/
theorem exact_tensor_add_left
    (f₁ f₂ : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct (f₁ + f₂) g =
      scalarSchwartzTensorProduct f₁ g + scalarSchwartzTensorProduct f₂ g :=
  scalarSchwartzTensorProduct_add_left f₁ f₂ g

/-- The exact right-additivity law cannot be replaced by a nonlinear second-factor operation. -/
theorem exact_tensor_add_right
    (f : 𝓢(E, ℂ)) (g₁ g₂ : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct f (g₁ + g₂) =
      scalarSchwartzTensorProduct f g₁ + scalarSchwartzTensorProduct f g₂ :=
  scalarSchwartzTensorProduct_add_right f g₁ g₂

/-- Exact scalar compatibility in the first factor is retained by the hostile surface. -/
theorem exact_tensor_smul_left
    (c : ℂ) (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct (c • f) g =
      c • scalarSchwartzTensorProduct f g :=
  scalarSchwartzTensorProduct_smul_left c f g

/-- Exact scalar compatibility in the second factor is retained by the hostile surface. -/
theorem exact_tensor_smul_right
    (c : ℂ) (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct f (c • g) =
      c • scalarSchwartzTensorProduct f g :=
  scalarSchwartzTensorProduct_smul_right c f g

end YangMills.Mathematics.Probes
