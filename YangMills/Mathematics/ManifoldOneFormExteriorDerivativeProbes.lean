/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormExteriorDerivative

/-!
# Probes for manifold one-form exterior-derivative certificates

These probes enforce the exact Cartan formula, its sign and bracket term, local uniqueness on smooth
fields, zero consistency, and agreement with Mathlib's normed-space `extDerivWithin` theorem.
-/

namespace YangMills.Mathematics.Probes

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
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}

/-- A certificate cannot violate its Cartan formula on an admissible local test. -/
theorem malformed_exteriorDerivative_cartanFormula_blocked
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second : (x : M) → TangentSpace I x)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (mismatch : coordinates (certificate.derivative.toForm x
      (ManifoldDifferentialForm.twoVectorArguments first second x)) ≠
      form.toForm.oneFormCartanExpressionCoordinates coordinates s x first second) : False :=
  mismatch (certificate.cartan_formula s x open_s mem_s unique_s
    first second first_smooth second_smooth)

/-- Swapping local vector fields must negate the Cartan expression. -/
theorem wrong_cartan_swap_sign_blocked
    (s : Set M) (x : M)
    (first second : (x : M) → TangentSpace I x)
    (mismatch : form.toForm.oneFormCartanExpressionCoordinates
        coordinates s x second first ≠
      -form.toForm.oneFormCartanExpressionCoordinates
        coordinates s x first second) : False :=
  mismatch (form.toForm.oneFormCartanExpressionCoordinates_swap
    coordinates s x first second)

/-- Omitting a nonzero Lie-bracket term is incompatible with the certified Cartan formula. -/
theorem missing_nonzero_cartan_bracketTerm_blocked
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second : (x : M) → TangentSpace I x)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (bracket_nonzero : coordinates (form.toForm x
      (fun _ => VectorField.mlieBracketWithin I first second s x)) ≠ 0)
    (omits_bracket : coordinates (certificate.derivative.toForm x
      (ManifoldDifferentialForm.twoVectorArguments first second x)) =
      (NormedSpace.fromTangentSpace
        (coordinates (form.toForm x (fun _ => second x))))
        (mfderivWithin I (modelWithCornersSelf ℝ W)
          (fun y => coordinates (form.toForm y (fun _ => second y))) s x (first x)) -
      (NormedSpace.fromTangentSpace
        (coordinates (form.toForm x (fun _ => first x))))
        (mfderivWithin I (modelWithCornersSelf ℝ W)
          (fun y => coordinates (form.toForm y (fun _ => first y))) s x (second x))) : False := by
  have cartan := certificate.cartan_formula s x open_s mem_s unique_s
    first second first_smooth second_smooth
  rw [omits_bracket] at cartan
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates at cartan
  apply bracket_nonzero
  exact sub_eq_self.mp cartan.symm

/-- Two certificates cannot be disconnected on the same admissible local smooth fields. -/
theorem disconnected_exteriorDerivative_certificates_blocked
    (firstCertificate secondCertificate :
      SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second : (x : M) → TangentSpace I x)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (disagree : coordinates (firstCertificate.derivative.toForm x
        (ManifoldDifferentialForm.twoVectorArguments first second x)) ≠
      coordinates (secondCertificate.derivative.toForm x
        (ManifoldDifferentialForm.twoVectorArguments first second x))) : False :=
  disagree (firstCertificate.derivatives_agree_on_smoothFields secondCertificate
    s x open_s mem_s unique_s first second first_smooth second_smooth)

/-- The zero one-form supplies a concrete exterior-derivative certificate. -/
theorem zero_exteriorDerivativeCertificate_exists :
    Nonempty (SmoothManifoldOneFormExteriorDerivativeCertificate coordinates
      (SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V) coordinates 1)) :=
  ⟨SmoothManifoldOneFormExteriorDerivativeCertificate.zero coordinates⟩

/-- On normed spaces, the certified Cartan expression is exactly Mathlib's local `extDerivWithin`. -/
theorem normedSpace_extDerivWithin_cartan_compatible
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    (normedForm : NormedSpaceDifferentialForm E' W' 1)
    (s : Set E') (x : E') (first second : E' → E')
    (form_differentiable : DifferentiableWithinAt ℝ normedForm s x)
    (first_differentiable : DifferentiableWithinAt ℝ first s x)
    (second_differentiable : DifferentiableWithinAt ℝ second s x)
    (unique : UniqueDiffWithinAt ℝ s x)
    (mismatch : extDerivWithin normedForm s x
        (ManifoldDifferentialForm.twoVectorArguments
          (I := modelWithCornersSelf ℝ E') first second x) ≠
      normedForm.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E') (ContinuousLinearEquiv.refl ℝ W')
        s x first second) : False :=
  mismatch (normedForm.extDerivWithin_eq_oneFormCartanExpression s x first second
    form_differentiable first_differentiable second_differentiable unique)

end YangMills.Mathematics.Probes
