/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormedSpacePositiveDegreeCartanNilpotence

/-!
# Hostile probes for normed-space positive-degree Cartan nilpotence

The probes lock the within-set theorem, its global specialization, the exact `1 → 2 → 3` endpoint,
and rejection of any nonzero value for the second exterior derivative's Cartan expression.
-/

namespace YangMills.Mathematics.NormedSpacePositiveDegreeCartanNilpotence.Probes

open Set

universe uE uW

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The within-set result uses the first derivative of the exact same input form. -/
theorem exact_within_nilpotence
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
      k s x fields = 0 :=
  form.extDerivWithin_positiveDegreeCartanExpression_zero s x fields
    form_regular regularity_order unique_s mem_closure_interior mem_s fields_differentiable

/-- The global result retains the exact first exterior derivative. -/
theorem exact_global_nilpotence
    {k : ℕ} (form : NormedSpaceDifferentialForm E W k)
    (x : E) (fields : Fin (k + 2) → E → E) {r : ℕ∞}
    (form_regular : ContDiffAt ℝ r form x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (fields_differentiable : ∀ i, DifferentiableAt ℝ (fields i) x) :
    let derivative : NormedSpaceDifferentialForm E W (k + 1) := extDeriv form
    derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
      (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
      k Set.univ x fields = 0 :=
  form.extDeriv_positiveDegreeCartanExpression_zero x fields
    form_regular regularity_order fields_differentiable

/-- The Bianchi-relevant ordinary exterior endpoint really has three vector-field slots. -/
theorem exact_one_two_three_endpoint
    (form : NormedSpaceDifferentialForm E W 1)
    (x : E) (fields : Fin 3 → E → E) {r : ℕ∞}
    (form_regular : ContDiffAt ℝ r form x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (fields_differentiable : ∀ i, DifferentiableAt ℝ (fields i) x) :
    let derivative : NormedSpaceDifferentialForm E W 2 := extDeriv form
    derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
      (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
      1 Set.univ x fields = 0 :=
  NormedSpaceDifferentialOneForm.secondExteriorDerivativeCartanExpression_zero
    form x fields form_regular regularity_order fields_differentiable

/-- A nonzero value for the exact second-derivative Cartan expression is impossible. -/
theorem nonzero_second_exterior_derivative_blocked
    (form : NormedSpaceDifferentialForm E W 1)
    (x : E) (fields : Fin 3 → E → E) {r : ℕ∞}
    (form_regular : ContDiffAt ℝ r form x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (fields_differentiable : ∀ i, DifferentiableAt ℝ (fields i) x)
    (claimed_nonzero :
      let derivative : NormedSpaceDifferentialForm E W 2 := extDeriv form
      derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        1 Set.univ x fields ≠ 0) : False :=
  claimed_nonzero
    (NormedSpaceDifferentialOneForm.secondExteriorDerivativeCartanExpression_zero
      form x fields form_regular regularity_order fields_differentiable)

/-- A claimed unrelated nonzero output cannot replace the proved zero expression. -/
theorem unrelated_nonzero_output_blocked
    (form : NormedSpaceDifferentialForm E W 1)
    (x : E) (fields : Fin 3 → E → E) {r : ℕ∞}
    (form_regular : ContDiffAt ℝ r form x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (fields_differentiable : ∀ i, DifferentiableAt ℝ (fields i) x)
    (other : W) (other_nonzero : other ≠ 0)
    (claimed :
      let derivative : NormedSpaceDifferentialForm E W 2 := extDeriv form
      derivative.toManifoldForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        1 Set.univ x fields = other) : False := by
  apply other_nonzero
  rw [← claimed]
  exact NormedSpaceDifferentialOneForm.secondExteriorDerivativeCartanExpression_zero
    form x fields form_regular regularity_order fields_differentiable

end YangMills.Mathematics.NormedSpacePositiveDegreeCartanNilpotence.Probes
