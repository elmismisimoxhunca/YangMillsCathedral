/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative

/-!
# Hostile probes for positive-degree manifold Cartan certificates

These probes lock Mathlib's exact triangular indices and signs, normed-space compatibility,
certificate agreement on smooth fields, the degree-two-to-three endpoint, rejection of malformed
formulas, and the concrete zero certificate.
-/

namespace YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

/-- The intrinsic expression reduces exactly to the normed-space Cartan sum. -/
theorem exact_normed_space_expression
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (form : NormedSpaceDifferentialForm E W (n + 1))
    (s : Set E) (x : E) (fields : Fin (n + 2) → E → E) :
    form.toManifoldForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        n s x fields =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        fderivWithin ℝ (fun y => form y (i.removeNth (fun k => fields k y)))
          s x (fields i x)) -
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, (-1 : ℤ) ^ (i + j : ℕ) •
        form x (Matrix.vecCons
          (VectorField.lieBracketWithin ℝ (fields i.castSucc) (fields j.succ) s x)
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k x))) :=
  ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_normedSpace
    n form s x fields

/-- Mathlib's local `extDerivWithin` is exactly the intrinsic expression under its hypotheses. -/
theorem exact_mathlib_extDerivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (form : NormedSpaceDifferentialForm E W (n + 1))
    (s : Set E) (x : E) (fields : Fin (n + 2) → E → E)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (fields_differentiable : ∀ i, DifferentiableWithinAt ℝ (fields i) s x)
    (unique : UniqueDiffWithinAt ℝ s x) :
    extDerivWithin form s x (fun i => fields i x) =
      form.toManifoldForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        n s x fields :=
  form.extDerivWithin_eq_positiveDegreeCartanExpression n s x fields
    form_differentiable fields_differentiable unique

variable {coordinates : V ≃L[ℝ] W} {n : ℕ}
variable {form : SmoothManifoldDifferentialForm I M V coordinates (n + 1)}

/-- The certificate retains its exact general Cartan formula. -/
theorem exact_certificate_formula
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      coordinates n form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    coordinates (certificate.derivative.toForm x (fun i => fields i x)) =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s x fields :=
  certificate.cartan_formula s x open_s mem_s unique_s fields fields_smooth

/-- Two certificates cannot disagree on any admissible tuple of smooth fields. -/
theorem disconnected_certificate_blocked
    (firstCertificate secondCertificate :
      SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (hne : coordinates (firstCertificate.derivative.toForm x (fun i => fields i x)) ≠
      coordinates (secondCertificate.derivative.toForm x (fun i => fields i x))) : False :=
  hne (firstCertificate.derivatives_agree_on_smoothFields secondCertificate
    s x open_s mem_s unique_s fields fields_smooth)

/-- The degree-two specialization has an exact smooth degree-three output. -/
theorem exact_two_to_three_endpoint
    {twoForm : SmoothManifoldDifferentialForm I M V coordinates 2}
    (certificate : SmoothManifoldTwoFormExteriorDerivativeCertificate coordinates twoForm) :
    ∃ output : SmoothManifoldDifferentialForm I M V coordinates 3,
      output.toForm = certificate.derivative.toForm :=
  ⟨certificate.derivative, rfl⟩

/-- Replacing the certified Cartan value at one admissible tuple is rejected. -/
theorem malformed_cartan_formula_blocked
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      coordinates n form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (mismatch : coordinates (certificate.derivative.toForm x (fun i => fields i x)) ≠
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s x fields) : False :=
  mismatch (certificate.cartan_formula s x open_s mem_s unique_s fields fields_smooth)

/-- The zero input has a concrete certificate whose output is exactly the zero form. -/
theorem exact_zero_certificate
    (coordinates : V ≃L[ℝ] W) (n : ℕ) :
    (SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.zero
      (I := I) (M := M) coordinates n).derivative.toForm = 0 :=
  rfl

end YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative.Probes
