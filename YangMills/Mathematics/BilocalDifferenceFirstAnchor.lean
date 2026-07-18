/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteConfigurationSchwartzTensor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bilocal difference coordinates with the first point as anchor

Reusable finite-dimensional infrastructure identifies an ordered pair `(x,y)` with `(x-y,x)`.
This is the source order used in Wilson's `C(x-y) O(x)` operator-product expansion. It is kept
separate from the general consecutive-difference/final-anchor equivalence used for translation-
invariant Wightman correlators.
-/

open scoped SchwartzMap

namespace YangMills.Mathematics

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Linear equivalence `(x,y) ↦ (x-y,x)`. -/
def bilocalDifferenceFirstAnchorLinearEquiv :
    (Fin 2 → E) ≃ₗ[ℝ] (E × E) where
  toFun x := (x 0 - x 1, x 0)
  invFun p := ![p.2, p.2 - p.1]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    apply Prod.ext <;> simp
  map_add' x y := by
    apply Prod.ext
    · simp
      abel
    · simp
  map_smul' c x := by
    apply Prod.ext <;> simp [smul_sub]

/-- The bilocal first-anchor equivalence is continuous linear in finite dimension. -/
noncomputable def bilocalDifferenceFirstAnchorContinuousLinearEquiv :
    (Fin 2 → E) ≃L[ℝ] (E × E) :=
  (bilocalDifferenceFirstAnchorLinearEquiv E).toContinuousLinearEquiv

@[simp] theorem bilocalDifferenceFirstAnchor_fst_apply (x : Fin 2 → E) :
    (bilocalDifferenceFirstAnchorContinuousLinearEquiv E x).1 = x 0 - x 1 :=
  rfl

@[simp] theorem bilocalDifferenceFirstAnchor_snd_apply (x : Fin 2 → E) :
    (bilocalDifferenceFirstAnchorContinuousLinearEquiv E x).2 = x 0 :=
  rfl

/-- Lift a relative `x-y` test and a first-anchor `x` test to ordered bilocal configuration space. -/
noncomputable def bilocalDifferenceFirstAnchorSchwartzLift
    (relative anchor : 𝓢(E, ℂ)) : 𝓢(Fin 2 → E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (bilocalDifferenceFirstAnchorContinuousLinearEquiv E)
    (scalarSchwartzTensorProduct relative anchor)

/-- Exact source-order evaluation `relative(x-y) * anchor(x)`. -/
@[simp] theorem bilocalDifferenceFirstAnchorSchwartzLift_apply
    (relative anchor : 𝓢(E, ℂ)) (x : Fin 2 → E) :
    bilocalDifferenceFirstAnchorSchwartzLift E relative anchor x =
      relative (x 0 - x 1) * anchor (x 0) :=
  rfl

end YangMills.Mathematics
