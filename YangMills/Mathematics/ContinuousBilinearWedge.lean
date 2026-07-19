/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupBracketCalculus
import YangMills.Mathematics.GradedLieBracketWedge
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Continuous bilinear wedge with a one-form

For a curried continuous bilinear map `B : V →L[ℝ] V →L[ℝ] V`, this module constructs the exact
one-form-with-`n`-form alternating wedge

`∑ᵢ (-1)ⁱ B(α(vᵢ), β(v₀,…,v̂ᵢ,…,vₙ))`.

The construction is additive and real-linear in both form arguments. For the actual
finite-dimensional group Lie algebra, postcomposition by the canonical tangent/model coordinates
is proved to carry the existing intrinsic Lie-bracket wedge to this operation with
`groupLieAlgebraCoordinateBracketCLM` exactly.

This supplies the coordinate wedge needed before differentiating `[A ∧ A]`. It does not itself
state an exterior-derivative Leibniz rule or Bianchi identity.
-/

namespace YangMills.Mathematics

universe uT uV uE uH uG

noncomputable section

variable
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Alternating wedge obtained by applying a continuous bilinear map to a continuous one-form and a
continuous `n`-form. -/
noncomputable def _root_.ContinuousAlternatingMap.continuousBilinearWedgeOneMany
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    T [⋀^Fin (n + 1)]→L[ℝ] V := by
  let alphaLinear : T →L[ℝ] V := {
    toFun := fun x => alpha (fun _ => x)
    map_add' := by
      intro x y
      have update_eq (z : T) :
          Function.update (fun _ : Fin 1 => 0) 0 z = fun _ => z := by
        funext i
        fin_cases i
        simp
      simpa only [update_eq] using alpha.map_update_add (fun _ : Fin 1 => 0) 0 x y
    map_smul' := by
      intro c x
      have update_eq (z : T) :
          Function.update (fun _ : Fin 1 => 0) 0 z = fun _ => z := by
        funext i
        fin_cases i
        simp
      simpa only [update_eq, RingHom.id_apply] using
        alpha.map_update_smul (fun _ : Fin 1 => 0) 0 c x
    cont := alpha.cont.comp (continuous_pi fun _ => continuous_id)
  }
  let partiallyApplied : T →ₗ[ℝ] T [⋀^Fin n]→ₗ[ℝ] V := {
    toFun := fun t => (bilinear (alphaLinear t)).toLinearMap.compAlternatingMap
      beta.toAlternatingMap
    map_add' := by
      intro x y
      ext v
      simp
    map_smul' := by
      intro c x
      ext v
      simp
  }
  let algebraic := AlternatingMap.alternatizeUncurryFin partiallyApplied
  let continuousMultilinear :
      ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => T) V := {
    toMultilinearMap := algebraic.toMultilinearMap
    cont := by
      have sum_continuous : Continuous (fun v : Fin (n + 1) → T =>
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
            bilinear (alphaLinear (v i)) (beta (i.removeNth v))) := by
        apply continuous_finsetSum
        intro i hi
        have remove_continuous : Continuous (fun v : Fin (n + 1) → T => i.removeNth v) :=
          continuous_pi fun j => continuous_apply (i.succAbove j)
        exact ((bilinear.continuous.comp
          (alphaLinear.cont.comp (continuous_apply i))).clm_apply
            (beta.cont.comp remove_continuous)).zsmul ((-1 : ℤ) ^ (i : ℕ))
      have algebraic_eq : (algebraic : (Fin (n + 1) → T) → V) =
          fun v => ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
            bilinear (alphaLinear (v i)) (beta (i.removeNth v)) := by
        funext v
        simp [algebraic, partiallyApplied, alphaLinear,
          AlternatingMap.alternatizeUncurryFin_apply]
      change Continuous (algebraic : (Fin (n + 1) → T) → V)
      rw [algebraic_eq]
      exact sum_continuous
  }
  exact {
    toContinuousMultilinearMap := continuousMultilinear
    map_eq_zero_of_eq' := algebraic.map_eq_zero_of_eq'
  }

/-- Exact omitted-slot evaluation formula. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T) :
    alpha.continuousBilinearWedgeOneMany bilinear n beta v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        bilinear (alpha (fun _ => v i)) (beta (i.removeNth v)) := by
  unfold ContinuousAlternatingMap.continuousBilinearWedgeOneMany
  change (AlternatingMap.alternatizeUncurryFin _) v = _
  rw [AlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- At degree one, the operation is the exact two-term antisymmetrization. -/
theorem _root_.ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) (v : Fin 2 → T) :
    alpha.continuousBilinearWedgeOneMany bilinear 1 beta v =
      bilinear (alpha (fun _ => v 0)) (beta (fun _ => v 1)) -
        bilinear (alpha (fun _ => v 1)) (beta (fun _ => v 0)) := by
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply, Fin.sum_univ_two]
  have remove_zero : Fin.removeNth 0 v = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  have remove_one : Fin.removeNth 1 v = fun _ : Fin 1 => v 0 := by
    funext i
    fin_cases i
    rfl
  rw [remove_zero, remove_one]
  simp [sub_eq_add_neg]

/-- Additivity in the one-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.add_continuousBilinearWedgeOneMany
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ)
    (alpha₁ alpha₂ : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    (alpha₁ + alpha₂).continuousBilinearWedgeOneMany bilinear n beta =
      alpha₁.continuousBilinearWedgeOneMany bilinear n beta +
        alpha₂.continuousBilinearWedgeOneMany bilinear n beta := by
  ext v
  simp [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply,
    Finset.sum_add_distrib]

/-- Additivity in the `n`-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.continuousBilinearWedgeOneMany_add
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta₁ beta₂ : T [⋀^Fin n]→L[ℝ] V) :
    alpha.continuousBilinearWedgeOneMany bilinear n (beta₁ + beta₂) =
      alpha.continuousBilinearWedgeOneMany bilinear n beta₁ +
        alpha.continuousBilinearWedgeOneMany bilinear n beta₂ := by
  ext v
  simp [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply,
    Finset.sum_add_distrib]

/-- Real scalar multiplication factors from the one-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.smul_continuousBilinearWedgeOneMany
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ) (r : ℝ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    (r • alpha).continuousBilinearWedgeOneMany bilinear n beta =
      r • alpha.continuousBilinearWedgeOneMany bilinear n beta := by
  ext v
  simp [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_comm]

/-- Real scalar multiplication factors from the `n`-form argument. -/
@[simp]
theorem _root_.ContinuousAlternatingMap.continuousBilinearWedgeOneMany_smul
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ) (r : ℝ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    alpha.continuousBilinearWedgeOneMany bilinear n (r • beta) =
      r • alpha.continuousBilinearWedgeOneMany bilinear n beta := by
  ext v
  simp [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical group Lie-algebra coordinate equivalence carries the intrinsic graded bracket
wedge to the continuous-bilinear coordinate wedge exactly. -/
theorem groupLieAlgebraCoordinateBracket_wedge_coherence
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] GroupLieAlgebra I G)
    (beta : T [⋀^Fin n]→L[ℝ] GroupLieAlgebra I G) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let coordinates := groupLieAlgebraModelEquiv (G := G) I
    coordinates.toContinuousLinearMap.compContinuousAlternatingMap
        (alpha.lieBracketWedgeOneMany n beta) =
      ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) n
        (coordinates.toContinuousLinearMap.compContinuousAlternatingMap alpha)
        (coordinates.toContinuousLinearMap.compContinuousAlternatingMap beta) := by
  dsimp only
  ext v
  change groupLieAlgebraModelEquiv (G := G) I
      (alpha.lieBracketWedgeOneMany n beta v) = _
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply,
    ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  rfl

end

end YangMills.Mathematics
