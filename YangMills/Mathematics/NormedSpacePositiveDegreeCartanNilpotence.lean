/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative

/-!
# Nilpotence of the positive-degree Cartan expression in normed spaces

Mathlib proves `extDerivWithin (extDerivWithin ω s) s = 0` under second-order regularity and the
usual set hypotheses. The project's positive-degree Cartan expression was proved to agree exactly
with `extDerivWithin`. This module composes those results: the positive-degree Cartan expression of
the first exterior derivative vanishes, both within a set and globally.

This is reusable local-model mathematics. It does not construct an exterior derivative on an
arbitrary manifold, prove chart independence there, or establish covariant `D²` or Bianchi.
-/

namespace YangMills.Mathematics

open Set

universe uE uW

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Under Mathlib's exact second-order and set hypotheses, the positive-degree Cartan expression of
`extDerivWithin ω s` is zero. The derivative's required differentiability is derived from the
regularity of `ω`; it is not supplied as an unrelated extra assumption. -/
theorem NormedSpaceDifferentialForm.extDerivWithin_positiveDegreeCartanExpression_zero
    {k : ℕ} (form : NormedSpaceDifferentialForm E W k)
    (s : Set E) (x : E) (fields : Fin (k + 2) → E → E) {r : ℕ∞}
    (form_regular : ContDiffWithinAt ℝ r form s x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (unique_s : UniqueDiffOn ℝ s)
    (mem_closure_interior : x ∈ closure (interior s))
    (mem_s : x ∈ s)
    (fields_differentiable : ∀ i, DifferentiableWithinAt ℝ (fields i) s x) :
    let derivative : NormedSpaceDifferentialForm E W (k + 1) := extDerivWithin form s
    derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
      (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
      k s x fields = 0 := by
  dsimp only
  let derivative : NormedSpaceDifferentialForm E W (k + 1) := extDerivWithin form s
  have derivative_differentiable :
      DifferentiableWithinAt ℝ (extDerivWithin form s) s x := by
    change DifferentiableWithinAt ℝ
      (fun y => ContinuousAlternatingMap.alternatizeUncurryFin
        (fderivWithin ℝ form s y)) s x
    apply (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E W).differentiableAt
      |>.comp_differentiableWithinAt x
    exact (form_regular.fderivWithin_right unique_s
      (le_minSmoothness.trans regularity_order) mem_s).differentiableWithinAt one_ne_zero
  have cartan_formula :=
    NormedSpaceDifferentialForm.extDerivWithin_eq_positiveDegreeCartanExpression
      k derivative s x fields derivative_differentiable fields_differentiable
      (unique_s.uniqueDiffWithinAt mem_s)
  rw [← cartan_formula]
  rw [extDerivWithin_extDerivWithin_apply form_regular regularity_order unique_s
    mem_closure_interior mem_s]
  rfl

/-- Global specialization of `extDerivWithin_positiveDegreeCartanExpression_zero`. -/
theorem NormedSpaceDifferentialForm.extDeriv_positiveDegreeCartanExpression_zero
    {k : ℕ} (form : NormedSpaceDifferentialForm E W k)
    (x : E) (fields : Fin (k + 2) → E → E) {r : ℕ∞}
    (form_regular : ContDiffAt ℝ r form x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (fields_differentiable : ∀ i, DifferentiableAt ℝ (fields i) x) :
    let derivative : NormedSpaceDifferentialForm E W (k + 1) := extDeriv form
    derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
      (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
      k Set.univ x fields = 0 := by
  simpa only [extDerivWithin_univ] using
    (form.extDerivWithin_positiveDegreeCartanExpression_zero Set.univ x fields
      form_regular.contDiffWithinAt regularity_order uniqueDiffOn_univ
      (by simp) (by simp) (fun i => (fields_differentiable i).differentiableWithinAt))

/-- The `1 → 2 → 3` specialization needed by the future local-model Bianchi calculation. -/
theorem NormedSpaceDifferentialOneForm.secondExteriorDerivativeCartanExpression_zero
    (form : NormedSpaceDifferentialForm E W 1)
    (x : E) (fields : Fin 3 → E → E) {r : ℕ∞}
    (form_regular : ContDiffAt ℝ r form x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (fields_differentiable : ∀ i, DifferentiableAt ℝ (fields i) x) :
    let derivative : NormedSpaceDifferentialForm E W 2 := extDeriv form
    derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
      (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
      1 Set.univ x fields = 0 := by
  simpa using form.extDeriv_positiveDegreeCartanExpression_zero x fields
    form_regular regularity_order fields_differentiable

end YangMills.Mathematics
