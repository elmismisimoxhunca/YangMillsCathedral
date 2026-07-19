/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzDirectionalEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

/-!
# Permutation symmetry of iterated Schwartz directional derivatives

Mathlib proves symmetry of the second Fréchet derivative under the standard smoothness hypothesis.
For Schwartz functions, this module upgrades that fact to arbitrary finite direction permutations.
It first proves that any two Schwartz line-derivative operators commute, identifies the recursive
iterated operator with a list fold, and applies permutation invariance of a fold by a
left-commutative operation.

This is reusable functional-analysis infrastructure and contains no Yang–Mills or
Osterwalder–Schrader assumption.
-/

namespace SchwartzMap

open LineDeriv

noncomputable section

/-- Two real directional-derivative operators commute on complex Schwartz functions. -/
theorem lineDerivOp_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (f : SchwartzMap E ℂ) :
    ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext x
  change (∂^{![v, w]} f) x = (∂^{![w, v]} f) x
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  exact (f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp) |>.iteratedFDeriv_cons

/-- The recursively defined iterated line-derivative operator is exactly the list fold of its
ordered direction tuple. -/
theorem iteratedLineDerivOp_eq_foldr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (directions : Fin n → E) (f : SchwartzMap E ℂ) :
    ∂^{directions} f =
      (List.ofFn directions).foldr (fun v g => ∂_{v} g) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left, List.ofFn_succ]
      change ∂_{directions 0} (∂^{Fin.tail directions} f) =
        ∂_{directions 0}
          ((List.ofFn fun i => directions i.succ).foldr (fun v g => ∂_{v} g) f)
      rw [ih (Fin.tail directions)]
      rfl

/-- The exact bundled iterated Schwartz line derivative is invariant under every permutation of its
direction slots. -/
theorem iteratedLineDerivOp_comp_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (directions : Fin n → E) (σ : Equiv.Perm (Fin n))
    (f : SchwartzMap E ℂ) :
    ∂^{directions ∘ σ} f = ∂^{directions} f := by
  rw [iteratedLineDerivOp_eq_foldr, iteratedLineDerivOp_eq_foldr]
  letI : LeftCommutative
      (fun v : E => fun g : SchwartzMap E ℂ => ∂_{v} g) :=
    ⟨fun v w g => lineDerivOp_commute v w g⟩
  exact (σ.ofFn_comp_perm directions).foldr_eq f

/-- Consequently, every iterated real Fréchet derivative of a complex Schwartz function is
invariant under permutation of its supplied directions. -/
theorem iteratedFDeriv_comp_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (directions : Fin n → E) (σ : Equiv.Perm (Fin n))
    (f : SchwartzMap E ℂ) (x : E) :
    iteratedFDeriv ℝ n (f : E → ℂ) x (directions ∘ σ) =
      iteratedFDeriv ℝ n (f : E → ℂ) x directions := by
  have h := congrArg (fun g : SchwartzMap E ℂ => g x)
    (iteratedLineDerivOp_comp_perm directions σ f)
  simpa only [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv] using h

end

end SchwartzMap
