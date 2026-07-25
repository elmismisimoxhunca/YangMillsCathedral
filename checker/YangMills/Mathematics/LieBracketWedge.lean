/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialForms
import Mathlib.Algebra.Lie.Basic

/-!
# Continuous Lie brackets and the bracket-wedge of one-forms

This module isolates the standard continuity requirement for a topological Lie algebra and builds
the degree-two bracket-wedge of two continuous one-forms. The construction is reusable algebraic
infrastructure; it does not define an exterior derivative or curvature.
-/

namespace YangMills.Mathematics

universe uE uH uM uT uV

/-- A topological Lie ring whose bracket is jointly continuous. -/
class ContinuousLieBracket (V : Type uV) [LieRing V] [TopologicalSpace V] : Prop where
  /-- Joint continuity of the bracket. -/
  continuous_bracket : Continuous fun pair : V × V => ⁅pair.1, pair.2⁆

variable
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousLieBracket V]
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]

/-- View a continuous alternating one-form as a continuous linear map in its sole input. -/
def _root_.ContinuousAlternatingMap.oneFormLinear
    (form : T [⋀^Fin 1]→L[ℝ] V) : T →L[ℝ] V where
  toFun x := form (fun _ => x)
  map_add' x y := by
    have update_eq (z : T) : Function.update (fun _ : Fin 1 => 0) 0 z = fun _ => z := by
      funext i
      fin_cases i
      simp
    simpa only [update_eq] using form.map_update_add (fun _ : Fin 1 => 0) 0 x y
  map_smul' c x := by
    have update_eq (z : T) : Function.update (fun _ : Fin 1 => 0) 0 z = fun _ => z := by
      funext i
      fin_cases i
      simp
    simpa only [update_eq, RingHom.id_apply] using
      form.map_update_smul (fun _ : Fin 1 => 0) 0 c x
  cont := form.cont.comp (continuous_pi fun _ => continuous_id)

/-- Antisymmetrized Lie bracket of two continuous one-forms.

With this convention, `[α ∧ α](v₀,v₁) = 2 • [α(v₀), α(v₁)]`, matching the factor
`1/2` in the standard curvature formula. -/
noncomputable def _root_.ContinuousAlternatingMap.lieBracketWedgeOne
    (first second : T [⋀^Fin 1]→L[ℝ] V) : T [⋀^Fin 2]→L[ℝ] V := by
  let firstLinear := first.oneFormLinear
  let secondLinear := second.oneFormLinear
  let value : (Fin 2 → T) → V := fun v =>
    ⁅firstLinear (v 0), secondLinear (v 1)⁆ -
      ⁅firstLinear (v 1), secondLinear (v 0)⁆
  let multilinear : MultilinearMap ℝ (fun _ : Fin 2 => T) V := {
    toFun := value
    map_update_add' := by
      intro _ m i x y
      fin_cases i <;>
        simp [value, firstLinear, secondLinear, add_lie, lie_add] <;> abel
    map_update_smul' := by
      intro _ m i c x
      fin_cases i <;>
        simp [value, firstLinear, secondLinear, lie_smul, smul_lie, smul_sub]
  }
  let continuousMultilinear : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => T) V := {
    toMultilinearMap := multilinear
    cont := by
      exact (ContinuousLieBracket.continuous_bracket.comp
          ((firstLinear.cont.comp (continuous_apply 0)).prodMk
            (secondLinear.cont.comp (continuous_apply 1)))).sub
        (ContinuousLieBracket.continuous_bracket.comp
          ((firstLinear.cont.comp (continuous_apply 1)).prodMk
            (secondLinear.cont.comp (continuous_apply 0))))
  }
  exact {
    toContinuousMultilinearMap := continuousMultilinear
    map_eq_zero_of_eq' := by
      intro v i j equal hij
      change value v = 0
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simp only [value]
        rw [show v 1 = v 0 from equal.symm]
        simp
      · simp only [value]
        rw [show v 1 = v 0 from equal]
        simp
      · exact (hij rfl).elim
  }

@[simp]
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOne_apply
    (first second : T [⋀^Fin 1]→L[ℝ] V) (v : Fin 2 → T) :
    first.lieBracketWedgeOne second v =
      ⁅first (fun _ => v 0), second (fun _ => v 1)⁆ -
        ⁅first (fun _ => v 1), second (fun _ => v 0)⁆ :=
  rfl

/-- The self bracket-wedge has the normalization used by `Ω = dΘ + 1/2 [Θ ∧ Θ]`. -/
theorem _root_.ContinuousAlternatingMap.lieBracketWedgeOne_self_apply
    (form : T [⋀^Fin 1]→L[ℝ] V) (v : Fin 2 → T) :
    form.lieBracketWedgeOne form v =
      (2 : ℝ) • ⁅form (fun _ => v 0), form (fun _ => v 1)⁆ := by
  rw [ContinuousAlternatingMap.lieBracketWedgeOne_apply, sub_eq_add_neg, lie_skew, two_smul]

/-- Pointwise bracket-wedge of two Lie-algebra-valued manifold one-forms. -/
noncomputable def ManifoldDifferentialForm.lieBracketWedgeOne
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (first second : ManifoldDifferentialForm I M V 1) :
    ManifoldDifferentialForm I M V 2 :=
  fun x => (first x).lieBracketWedgeOne (second x)

@[simp]
theorem ManifoldDifferentialForm.lieBracketWedgeOne_apply
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (first second : ManifoldDifferentialForm I M V 1) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    first.lieBracketWedgeOne second x v =
      ⁅first x (fun _ => v 0), second x (fun _ => v 1)⁆ -
        ⁅first x (fun _ => v 1), second x (fun _ => v 0)⁆ :=
  rfl

end YangMills.Mathematics
