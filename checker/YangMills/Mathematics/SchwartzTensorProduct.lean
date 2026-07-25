/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Tensor products of scalar Schwartz functions

This reusable infrastructure proves that `(x,y) ↦ f(x)g(y)` is a Schwartz function whenever `f`
and `g` are complex scalar Schwartz functions on real normed spaces. The proof gives explicit decay
bounds in Mathlib's weighted Fréchet-derivative seminorms.

The operation is algebraic at this stage. Packaging it as a continuous bilinear map for the Schwartz
topologies is separate work.
-/

open scoped SchwartzMap

namespace YangMills.Mathematics

variable {E D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Pullback through the first product projection does not increase an iterated derivative norm. -/
lemma norm_iteratedFDeriv_comp_fst_le
    (f : 𝓢(E, ℂ)) (r : ℕ) (z : E × D) :
    ‖iteratedFDeriv ℝ r (fun z : E × D => f z.1) z‖ ≤
      ‖iteratedFDeriv ℝ r f z.1‖ := by
  change ‖iteratedFDeriv ℝ r
    (f ∘ ContinuousLinearMap.fst ℝ E D) z‖ ≤ _
  rw [(ContinuousLinearMap.fst ℝ E D).iteratedFDeriv_comp_right
    (f.smooth r) z le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ r f z.1‖ *
        ∏ _ : Fin r, ‖ContinuousLinearMap.fst ℝ E D‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ r f z.1‖ * 1 := by
      gcongr
      apply Finset.prod_le_one
      · intro i hi
        positivity
      · intro i hi
        exact ContinuousLinearMap.norm_fst_le ℝ E D
    _ = _ := mul_one _

/-- Pullback through the second product projection does not increase an iterated derivative norm. -/
lemma norm_iteratedFDeriv_comp_snd_le
    (g : 𝓢(D, ℂ)) (r : ℕ) (z : E × D) :
    ‖iteratedFDeriv ℝ r (fun z : E × D => g z.2) z‖ ≤
      ‖iteratedFDeriv ℝ r g z.2‖ := by
  change ‖iteratedFDeriv ℝ r
    (g ∘ ContinuousLinearMap.snd ℝ E D) z‖ ≤ _
  rw [(ContinuousLinearMap.snd ℝ E D).iteratedFDeriv_comp_right
    (g.smooth r) z le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ r g z.2‖ *
        ∏ _ : Fin r, ‖ContinuousLinearMap.snd ℝ E D‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ r g z.2‖ * 1 := by
      gcongr
      apply Finset.prod_le_one
      · intro i hi
        positivity
      · intro i hi
        exact ContinuousLinearMap.norm_snd_le ℝ E D
    _ = _ := mul_one _

/-- A power of a product maximum is bounded by the sum of the corresponding powers. -/
lemma max_pow_le_add_pow
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    max a b ^ k ≤ a ^ k + b ^ k := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact le_add_of_nonneg_left (pow_nonneg ha _)
  · rw [max_eq_left hba]
    exact le_add_of_nonneg_right (pow_nonneg hb _)

/-- The scalar tensor product of two complex Schwartz functions. -/
noncomputable def scalarSchwartzTensorProduct
    (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) : 𝓢(E × D, ℂ) where
  toFun := fun z => f z.1 * g z.2
  smooth' := by
    fun_prop
  decay' k n := by
    let C : ℝ :=
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((SchwartzMap.seminorm ℂ k i) f *
            (SchwartzMap.seminorm ℂ 0 (n - i)) g +
          (SchwartzMap.seminorm ℂ 0 i) f *
            (SchwartzMap.seminorm ℂ k (n - i)) g)
    refine ⟨C, fun z => ?_⟩
    have hfsm : ContDiff ℝ n (fun z : E × D => f z.1) :=
      (f.smooth n).comp (ContinuousLinearMap.fst ℝ E D).contDiff
    have hgsm : ContDiff ℝ n (fun z : E × D => g z.2) :=
      (g.smooth n).comp (ContinuousLinearMap.snd ℝ E D).contDiff
    have hmul := norm_iteratedFDeriv_mul_le hfsm hgsm z (by exact le_rfl)
    calc
      ‖z‖ ^ k *
          ‖iteratedFDeriv ℝ n
            (fun z : E × D => f z.1 * g z.2) z‖
          ≤ ‖z‖ ^ k *
            ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i
                (fun z : E × D => f z.1) z‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : E × D => g z.2) z‖ := by
            exact mul_le_mul_of_nonneg_left hmul
              (pow_nonneg (norm_nonneg _) _)
      _ = ∑ i ∈ Finset.range (n + 1),
            ‖z‖ ^ k *
              ((n.choose i : ℝ) *
                ‖iteratedFDeriv ℝ i
                  (fun z : E × D => f z.1) z‖ *
                ‖iteratedFDeriv ℝ (n - i)
                  (fun z : E × D => g z.2) z‖) := by
            rw [Finset.mul_sum]
      _ ≤ C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Prod.norm_def]
        have hmax :=
          max_pow_le_add_pow ‖z.1‖ ‖z.2‖
            (norm_nonneg _) (norm_nonneg _) k
        have hfi :=
          norm_iteratedFDeriv_comp_fst_le (D := D) f i z
        have hgi :=
          norm_iteratedFDeriv_comp_snd_le (E := E) g (n - i) z
        have hfk :=
          SchwartzMap.le_seminorm ℂ k i f z.1
        have hf0 :=
          SchwartzMap.le_seminorm ℂ 0 i f z.1
        have hgk :=
          SchwartzMap.le_seminorm ℂ k (n - i) g z.2
        have hg0 :=
          SchwartzMap.le_seminorm ℂ 0 (n - i) g z.2
        rw [pow_zero, one_mul] at hf0 hg0
        calc
          max ‖z.1‖ ‖z.2‖ ^ k *
                ((n.choose i : ℝ) *
                  ‖iteratedFDeriv ℝ i
                    (fun z : E × D => f z.1) z‖ *
                  ‖iteratedFDeriv ℝ (n - i)
                    (fun z : E × D => g z.2) z‖)
              ≤ (‖z.1‖ ^ k + ‖z.2‖ ^ k) *
                ((n.choose i : ℝ) *
                  ‖iteratedFDeriv ℝ i f z.1‖ *
                  ‖iteratedFDeriv ℝ (n - i) g z.2‖) := by
                gcongr
          _ = (n.choose i : ℝ) *
                ((‖z.1‖ ^ k *
                    ‖iteratedFDeriv ℝ i f z.1‖) *
                    ‖iteratedFDeriv ℝ (n - i) g z.2‖ +
                  ‖iteratedFDeriv ℝ i f z.1‖ *
                    (‖z.2‖ ^ k *
                      ‖iteratedFDeriv ℝ (n - i) g z.2‖)) := by
                ring
          _ ≤ (n.choose i : ℝ) *
                ((SchwartzMap.seminorm ℂ k i) f *
                    (SchwartzMap.seminorm ℂ 0 (n - i)) g +
                  (SchwartzMap.seminorm ℂ 0 i) f *
                    (SchwartzMap.seminorm ℂ k (n - i)) g) := by
                gcongr

/-- The bundled tensor product evaluates as the product of factor evaluations. -/
@[simp] theorem scalarSchwartzTensorProduct_apply
    (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) (z : E × D) :
    scalarSchwartzTensorProduct f g z = f z.1 * g z.2 :=
  rfl

/-- Tensor product is additive in its first factor. -/
theorem scalarSchwartzTensorProduct_add_left
    (f₁ f₂ : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct (f₁ + f₂) g =
      scalarSchwartzTensorProduct f₁ g + scalarSchwartzTensorProduct f₂ g := by
  ext z
  simp [add_mul]

/-- Tensor product is additive in its second factor. -/
theorem scalarSchwartzTensorProduct_add_right
    (f : 𝓢(E, ℂ)) (g₁ g₂ : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct f (g₁ + g₂) =
      scalarSchwartzTensorProduct f g₁ + scalarSchwartzTensorProduct f g₂ := by
  ext z
  simp [mul_add]

/-- Tensor product respects scalar multiplication in its first factor. -/
theorem scalarSchwartzTensorProduct_smul_left
    (c : ℂ) (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct (c • f) g =
      c • scalarSchwartzTensorProduct f g := by
  ext z
  simp [smul_eq_mul, mul_assoc]

/-- Tensor product respects scalar multiplication in its second factor. -/
theorem scalarSchwartzTensorProduct_smul_right
    (c : ℂ) (f : 𝓢(E, ℂ)) (g : 𝓢(D, ℂ)) :
    scalarSchwartzTensorProduct f (c • g) =
      c • scalarSchwartzTensorProduct f g := by
  ext z
  simp [smul_eq_mul, mul_left_comm]

end YangMills.Mathematics
