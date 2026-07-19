/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative

/-!
# Bridge between one-form and positive-degree Cartan certificates

The general positive-degree certificate includes index `n = 0`, but its triangular formula and field
family presentation were introduced independently of the earlier specialized one-form certificate.
This module proves their Cartan expressions coincide exactly and supplies conversions in both
directions that preserve the same smooth degree-two derivative carrier.

This is coherence between supplied certificate APIs. It neither proves existence of a certificate
nor turns either presentation into a canonical global exterior derivative.
-/

namespace YangMills.Mathematics

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

/-- Package two tangent fields as the exact `Fin 2` field family used by the positive-degree
formula. -/
def ManifoldDifferentialForm.twoTangentFieldFamily
    (first second : (x : M) → TangentSpace I x) :
    Fin 2 → (x : M) → TangentSpace I x :=
  Fin.cases first (fun _ => second)

omit [IsManifold I ∞ M] in
/-- At `n = 0`, the positive-degree triangular Cartan expression is exactly the earlier ordered
one-form Cartan expression. -/
theorem ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_zero_eq_oneForm
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (s : Set M) (x : M)
    (first second : (x : M) → TangentSpace I x) :
    form.positiveDegreeCartanExpressionCoordinates coordinates 0 s x
        (twoTangentFieldFamily first second) =
      form.oneFormCartanExpressionCoordinates coordinates s x first second := by
  have field_zero (y : M) : twoTangentFieldFamily first second 0 y = first y := rfl
  have field_one (y : M) : twoTangentFieldFamily first second 1 y = second y := rfl
  have remove_zero (y : M) :
      Fin.removeNth 0 (fun k => twoTangentFieldFamily first second k y) =
        fun _ : Fin 1 => second y := by
    funext i
    fin_cases i
    rfl
  have remove_one (y : M) :
      Fin.removeNth 1 (fun k => twoTangentFieldFamily first second k y) =
        fun _ : Fin 1 => first y := by
    funext i
    fin_cases i
    rfl
  have upper_interval : Finset.Ici (0 : Fin 1) = Finset.univ := by
    ext j
    fin_cases j
    simp
  have coefficient_zero :
      (fun y => coordinates (form y (Fin.removeNth 0
        (fun k => twoTangentFieldFamily first second k y)))) =
        fun y => coordinates (form y (fun _ : Fin 1 => second y)) := by
    funext y
    rw [remove_zero y]
  have coefficient_one :
      (fun y => coordinates (form y (Fin.removeNth 1
        (fun k => twoTangentFieldFamily first second k y)))) =
        fun y => coordinates (form y (fun _ : Fin 1 => first y)) := by
    funext y
    rw [remove_one y]
  have fields_zero : twoTangentFieldFamily first second 0 = first := funext field_zero
  have fields_one : twoTangentFieldFamily first second 1 = second := funext field_one
  have vecCons_empty (z : TangentSpace I x) (tail : Fin 0 → TangentSpace I x) :
      Matrix.vecCons z tail = fun _ : Fin 1 => z := by
    funext i
    fin_cases i
    rfl
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
  rw [Fin.sum_univ_two]
  rw [remove_zero x, remove_one x, coefficient_zero, coefficient_one,
    fields_zero, fields_one]
  rw [Fin.sum_univ_one, upper_interval]
  simp [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates,
    vecCons_empty, sub_eq_add_neg]
  rw [fields_zero, fields_one]

/-- Convert the specialized one-form certificate to the `n = 0` positive-degree presentation while
retaining the identical smooth degree-two derivative. -/
noncomputable def SmoothManifoldOneFormExteriorDerivativeCertificate.toPositiveDegreeZero
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form) :
    SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form where
  derivative := certificate.derivative
  cartan_formula := by
    intro s x open_s mem_s unique_s fields fields_smooth
    let first := fields 0
    let second := fields 1
    have fields_eq : fields =
        ManifoldDifferentialForm.twoTangentFieldFamily first second := by
      funext i
      fin_cases i <;> rfl
    rw [fields_eq] at fields_smooth ⊢
    rw [ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_zero_eq_oneForm]
    convert certificate.cartan_formula s x open_s mem_s unique_s
      first second (fields_smooth 0) (fields_smooth 1) using 1
    apply congrArg coordinates
    apply congrArg (certificate.derivative.toForm x)
    funext i
    fin_cases i <;> rfl

/-- Convert an `n = 0` positive-degree certificate to the specialized one-form presentation while
retaining the identical smooth degree-two derivative. -/
noncomputable def SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.toOneForm
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form) :
    SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form where
  derivative := certificate.derivative
  cartan_formula := by
    intro s x open_s mem_s unique_s first second first_smooth second_smooth
    have formula := certificate.cartan_formula s x open_s mem_s unique_s
      (ManifoldDifferentialForm.twoTangentFieldFamily first second) (by
        intro i
        fin_cases i
        · exact first_smooth
        · exact second_smooth)
    rw [ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_zero_eq_oneForm]
      at formula
    convert formula using 1
    apply congrArg coordinates
    apply congrArg (certificate.derivative.toForm x)
    funext i
    fin_cases i <;> rfl

/-- The forward conversion retains the exact derivative carrier. -/
@[simp]
theorem SmoothManifoldOneFormExteriorDerivativeCertificate.toPositiveDegreeZero_derivative
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form) :
    certificate.toPositiveDegreeZero.derivative = certificate.derivative :=
  rfl

/-- The reverse conversion retains the exact derivative carrier. -/
@[simp]
theorem SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.toOneForm_derivative
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form) :
    certificate.toOneForm.derivative = certificate.derivative :=
  rfl

end YangMills.Mathematics
