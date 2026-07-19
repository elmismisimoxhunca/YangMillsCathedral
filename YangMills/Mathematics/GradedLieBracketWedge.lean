/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieBracketWedge
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Graded Lie-bracket wedge with a one-form

This module extends the existing degree-one bracket wedge to the operation
`[α ∧ β] : Ω¹(T;V) × Ωⁿ(T;V) → Ωⁿ⁺¹(T;V)`. It uses Mathlib's algebraic
`AlternatingMap.alternatizeUncurryFin` and separately proves continuity of the exact alternating
sum. No normed-space assumption is added.

The convention is
`∑ᵢ (-1)ⁱ [α(vᵢ), β(v₀,…,v̂ᵢ,…,vₙ)]`. At degree one it is proved equal to the previously fixed
two-term convention, hence preserves the factor-two self-wedge normalization used in curvature.
This is reusable algebraic/topological infrastructure; it does not define an exterior derivative,
a covariant exterior derivative, or Bianchi.
-/

namespace YangMills.Mathematics

universe uE uH uM uT uV

noncomputable section

variable
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousLieBracket V]
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]

/-- Graded bracket wedge of a continuous one-form with a continuous `n`-form. -/
noncomputable def _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    T [⋀^Fin (n + 1)]→L[ℝ] V := by
  let bracketLinear : V →ₗ[ℝ] V →ₗ[ℝ] V :=
    LinearMap.mk₂ ℝ (fun x y => ⁅x, y⁆) add_lie smul_lie lie_add lie_smul
  let postcomposeBeta : (V →ₗ[ℝ] V) →ₗ[ℝ] T [⋀^Fin n]→ₗ[ℝ] V := {
    toFun := fun g => g.compAlternatingMap beta.toAlternatingMap
    map_add' := by
      intro g h
      ext v
      simp
    map_smul' := by
      intro c g
      ext v
      simp
  }
  let partiallyBracketed : T →ₗ[ℝ] T [⋀^Fin n]→ₗ[ℝ] V :=
    postcomposeBeta.comp (bracketLinear.comp alpha.oneFormLinear.toLinearMap)
  let algebraic := AlternatingMap.alternatizeUncurryFin partiallyBracketed
  let continuousMultilinear : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => T) V := {
    toMultilinearMap := algebraic.toMultilinearMap
    cont := by
      have sum_continuous : Continuous (fun v : Fin (n + 1) → T =>
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
            ⁅alpha.oneFormLinear (v i), beta (i.removeNth v)⁆) := by
        apply continuous_finsetSum
        intro i hi
        have remove_continuous : Continuous (fun v : Fin (n + 1) → T => i.removeNth v) :=
          continuous_pi fun j => continuous_apply (i.succAbove j)
        exact (ContinuousLieBracket.continuous_bracket.comp
          ((alpha.oneFormLinear.cont.comp (continuous_apply i)).prodMk
            (beta.cont.comp remove_continuous))).zsmul ((-1 : ℤ) ^ (i : ℕ))
      have algebraic_eq : (algebraic : (Fin (n + 1) → T) → V) =
          fun v => ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
            ⁅alpha.oneFormLinear (v i), beta (i.removeNth v)⁆ := by
        funext v
        simp [algebraic, partiallyBracketed, postcomposeBeta, bracketLinear,
          AlternatingMap.alternatizeUncurryFin_apply]
      change Continuous (algebraic : (Fin (n + 1) → T) → V)
      rw [algebraic_eq]
      exact sum_continuous
  }
  exact {
    toContinuousMultilinearMap := continuousMultilinear
    map_eq_zero_of_eq' := algebraic.map_eq_zero_of_eq'
  }

/-- Exact alternating-sum evaluation formula for the graded bracket wedge. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany_apply
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T) :
    alpha.lieBracketWedgeOneMany n beta v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        ⁅alpha (fun _ => v i), beta (i.removeNth v)⁆ := by
  unfold ContinuousAlternatingMap.lieBracketWedgeOneMany
  change (AlternatingMap.alternatizeUncurryFin _) v = _
  rw [AlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- At degree one, the graded construction is exactly the existing two-term bracket wedge. -/
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany_one
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany 1 beta = alpha.lieBracketWedgeOne beta := by
  ext v
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply,
    ContinuousAlternatingMap.lieBracketWedgeOne_apply, Fin.sum_univ_two]
  have hzero : Fin.removeNth 0 v = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  have hone : Fin.removeNth 1 v = fun _ : Fin 1 => v 0 := by
    funext i
    fin_cases i
    rfl
  rw [hzero, hone]
  simp [sub_eq_add_neg]

/-- The cubic self-bracket vanishes by the Lie Jacobi identity. With the project's exact
self-wedge normalization, evaluation expands to twice the cyclic Jacobi sum. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany_self_self
    (alpha : T [⋀^Fin 1]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany 2 (alpha.lieBracketWedgeOne alpha) = 0 := by
  ext v
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply, Fin.sum_univ_three]
  simp only [ContinuousAlternatingMap.lieBracketWedgeOne_apply]
  simp [Fin.removeNth]
  rw [show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = (1 : Fin 3) by decide]
  have pair_eq (x y z : V) : ⁅x, ⁅y, z⁆⁆ - ⁅x, ⁅z, y⁆⁆ =
      (2 : ℤ) • ⁅x, ⁅y, z⁆⁆ := by
    rw [← lie_skew z y, lie_neg, sub_neg_eq_add, two_zsmul]
  rw [pair_eq, pair_eq, pair_eq, ← zsmul_add, ← zsmul_add, lie_jacobi, smul_zero]

/-- The graded bracket wedge is additive in its one-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.add_lieBracketWedgeOneMany
    (n : ℕ) (alpha₁ alpha₂ : T [⋀^Fin 1]→L[ℝ] V)
    (beta : T [⋀^Fin n]→L[ℝ] V) :
    (alpha₁ + alpha₂).lieBracketWedgeOneMany n beta =
      alpha₁.lieBracketWedgeOneMany n beta + alpha₂.lieBracketWedgeOneMany n beta := by
  ext v
  simp [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply, add_lie,
    Finset.sum_add_distrib]

/-- The graded bracket wedge is additive in its `n`-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany_add
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V)
    (beta₁ beta₂ : T [⋀^Fin n]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany n (beta₁ + beta₂) =
      alpha.lieBracketWedgeOneMany n beta₁ + alpha.lieBracketWedgeOneMany n beta₂ := by
  ext v
  simp [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply, lie_add,
    Finset.sum_add_distrib]

/-- Real scalar multiplication factors from the one-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.smul_lieBracketWedgeOneMany
    [ContinuousSMul ℝ V]
    (n : ℕ) (r : ℝ) (alpha : T [⋀^Fin 1]→L[ℝ] V)
    (beta : T [⋀^Fin n]→L[ℝ] V) :
    (r • alpha).lieBracketWedgeOneMany n beta =
      r • alpha.lieBracketWedgeOneMany n beta := by
  ext v
  simp [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply, smul_lie,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_comm]

/-- Real scalar multiplication factors from the `n`-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany_smul
    [ContinuousSMul ℝ V]
    (n : ℕ) (r : ℝ) (alpha : T [⋀^Fin 1]→L[ℝ] V)
    (beta : T [⋀^Fin n]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany n (r • beta) =
      r • alpha.lieBracketWedgeOneMany n beta := by
  ext v
  simp [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply, lie_smul,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_comm]

/-- A zero one-form has zero graded bracket wedge in every degree. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.zero_lieBracketWedgeOneMany
    (n : ℕ) (beta : T [⋀^Fin n]→L[ℝ] V) :
    (0 : T [⋀^Fin 1]→L[ℝ] V).lieBracketWedgeOneMany n beta = 0 := by
  ext v
  simp

/-- Bracketing with a zero `n`-form gives zero in every degree. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOneMany_zero
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany n 0 = 0 := by
  ext v
  simp

/-- Pointwise graded bracket wedge of a one-form with an `n`-form on a manifold. -/
noncomputable def ManifoldDifferentialForm.lieBracketWedgeOneMany
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (n : ℕ) (alpha : ManifoldDifferentialForm I M V 1)
    (beta : ManifoldDifferentialForm I M V n) :
    ManifoldDifferentialForm I M V (n + 1) :=
  fun x => (alpha x).lieBracketWedgeOneMany n (beta x)

/-- The manifold lift retains the exact pointwise alternating-sum formula. -/
@[simp]
theorem ManifoldDifferentialForm.lieBracketWedgeOneMany_apply
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (n : ℕ) (alpha : ManifoldDifferentialForm I M V 1)
    (beta : ManifoldDifferentialForm I M V n) (x : M)
    (v : Fin (n + 1) → TangentSpace I x) :
    alpha.lieBracketWedgeOneMany n beta x v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        ⁅alpha x (fun _ => v i), beta x (i.removeNth v)⁆ :=
  ContinuousAlternatingMap.lieBracketWedgeOneMany_apply n (alpha x) (beta x) v

/-- The pointwise manifold cubic self-bracket is the zero three-form. -/
@[simp]
theorem ManifoldDifferentialForm.lieBracketWedgeOneMany_self_self
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (alpha : ManifoldDifferentialForm I M V 1) :
    alpha.lieBracketWedgeOneMany 2 (alpha.lieBracketWedgeOne alpha) = 0 := by
  funext x
  exact ContinuousAlternatingMap.lieBracketWedgeOneMany_self_self (alpha x)

end

end YangMills.Mathematics
