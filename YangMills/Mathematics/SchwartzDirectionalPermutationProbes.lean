/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzDirectionalPermutation

/-!
# Hostile probes for Schwartz directional permutation symmetry

The probes lock commutation and arbitrary permutation to the same Schwartz function, point, and
ordered direction tuple rather than to an unrelated symmetric functional.
-/

namespace SchwartzMap.DirectionalPermutation.Probes

open LineDeriv

noncomputable section

/-- The two-slot swap is the exact Clairaut commutation law on the same Schwartz function. -/
theorem exact_two_direction_commutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (f : SchwartzMap E ℂ) :
    ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) :=
  SchwartzMap.lineDerivOp_commute v w f

/-- Arbitrary permutation retains the exact iterated line-derivative Schwartz function. -/
theorem exact_iterated_operator_permutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (directions : Fin n → E) (σ : Equiv.Perm (Fin n))
    (f : SchwartzMap E ℂ) :
    ∂^{directions ∘ σ} f = ∂^{directions} f :=
  SchwartzMap.iteratedLineDerivOp_comp_perm directions σ f

/-- Arbitrary permutation retains the exact iterated Fréchet value at the designated point. -/
theorem exact_iterated_frechet_permutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (directions : Fin n → E) (σ : Equiv.Perm (Fin n))
    (f : SchwartzMap E ℂ) (x : E) :
    iteratedFDeriv ℝ n (f : E → ℂ) x (directions ∘ σ) =
      iteratedFDeriv ℝ n (f : E → ℂ) x directions :=
  SchwartzMap.iteratedFDeriv_comp_perm directions σ f x

/-- A nonzero iterated jet cannot be changed to zero merely by permuting its direction slots. -/
theorem nonzero_jet_survives_permutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (directions : Fin n → E) (σ : Equiv.Perm (Fin n))
    (f : SchwartzMap E ℂ) (x : E)
    (hne : iteratedFDeriv ℝ n (f : E → ℂ) x directions ≠ 0) :
    iteratedFDeriv ℝ n (f : E → ℂ) x (directions ∘ σ) ≠ 0 := by
  rw [SchwartzMap.iteratedFDeriv_comp_perm directions σ f x]
  exact hne

end

end SchwartzMap.DirectionalPermutation.Probes
