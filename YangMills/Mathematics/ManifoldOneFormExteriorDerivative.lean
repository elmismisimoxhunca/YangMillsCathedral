/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormedSpaceExteriorDerivative
import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Cartan certificates for exterior derivatives of manifold one-forms

Mathlib currently provides `extDeriv` on normed spaces but not a global arbitrary-manifold exterior
derivative. This module isolates a reusable, explicitly certified `1 → 2` interface based on the
intrinsic Cartan formula

`dω(X,Y) = D(ω(Y))·X - D(ω(X))·Y - ω([X,Y])`.

The derivative is called a certificate until existence and full uniqueness on arbitrary manifolds
are proved. It is standard differential-geometric infrastructure, not a Yang–Mills witness.
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

namespace ManifoldTangentField

/-- A tangent-vector field is smooth on `s` when its section of the tangent bundle is smooth there. -/
def IsSmoothOn (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (s : Set M) (field : (x : M) → TangentSpace I x) : Prop :=
  ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞
    (fun x => (⟨x, field x⟩ : TangentBundle I M)) s

end ManifoldTangentField

/-- Put two tangent fields into the ordered `Fin 2` argument tuple at `x`. -/
def ManifoldDifferentialForm.twoVectorArguments
    (first second : (x : M) → TangentSpace I x) (x : M) : Fin 2 → TangentSpace I x :=
  Fin.cases (first x) (fun _ => second x)

/-- The coordinate-valued Cartan expression for the exterior derivative of a manifold one-form. -/
noncomputable def ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (s : Set M) (x : M)
    (first second : (x : M) → TangentSpace I x) : W :=
  (NormedSpace.fromTangentSpace (coordinates (form x (fun _ => second x))))
      (mfderivWithin I (modelWithCornersSelf ℝ W)
        (fun y => coordinates (form y (fun _ => second y))) s x (first x)) -
    (NormedSpace.fromTangentSpace (coordinates (form x (fun _ => first x))))
      (mfderivWithin I (modelWithCornersSelf ℝ W)
        (fun y => coordinates (form y (fun _ => first y))) s x (second x)) -
    coordinates
      (form x (fun _ => VectorField.mlieBracketWithin I first second s x))

omit [IsManifold I ∞ M] in
/-- Swapping the two vector fields negates the Cartan expression. -/
theorem ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_swap
    (coordinates : V ≃L[ℝ] W) (form : ManifoldDifferentialForm I M V 1)
    (s : Set M) (x : M)
    (first second : (x : M) → TangentSpace I x) :
    form.oneFormCartanExpressionCoordinates coordinates s x second first =
      -form.oneFormCartanExpressionCoordinates coordinates s x first second := by
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
  rw [VectorField.mlieBracketWithin_swap_apply (V := second) (W := first)]
  let bracket := VectorField.mlieBracketWithin I first second s x
  have update_eq (z : TangentSpace I x) :
      Function.update (fun _ : Fin 1 => 0) 0 z = fun _ => z := by
    funext i
    fin_cases i
    simp
  have form_neg : form x (fun _ => -bracket) = -form x (fun _ => bracket) := by
    simpa only [update_eq, neg_smul, one_smul, RingHom.id_apply] using
      (form x).map_update_smul (fun _ : Fin 1 => 0) 0 (-1 : ℝ) bracket
  have bracket_neg : coordinates (form x (fun _ => -bracket)) =
      -coordinates (form x (fun _ => bracket)) := by
    rw [form_neg, map_neg]
  rw [bracket_neg]
  abel

/-- In canonical normed-space coordinates, the manifold Cartan expression is the usual
`fderivWithin`/`lieBracketWithin` expression. -/
theorem ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_normedSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (form : NormedSpaceDifferentialForm E W 1) (s : Set E) (x : E)
    (first second : E → E) :
    form.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        s x first second =
      fderivWithin ℝ (fun y => form y (fun _ => second y)) s x (first x) -
      fderivWithin ℝ (fun y => form y (fun _ => first y)) s x (second x) -
      form x (fun _ => VectorField.lieBracketWithin ℝ first second s x) := by
  simp only [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates,
    NormedSpaceDifferentialForm.toManifoldForm, mfderivWithin_eq_fderivWithin,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    ContinuousLinearEquiv.refl_apply]
  rfl

/-- Mathlib's local normed-space exterior derivative satisfies the same ordered Cartan formula. -/
theorem NormedSpaceDifferentialForm.extDerivWithin_eq_oneFormCartanExpression
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (form : NormedSpaceDifferentialForm E W 1) (s : Set E) (x : E)
    (first second : E → E)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (first_differentiable : DifferentiableWithinAt ℝ first s x)
    (second_differentiable : DifferentiableWithinAt ℝ second s x)
    (unique : UniqueDiffWithinAt ℝ s x) :
    extDerivWithin form s x
        (ManifoldDifferentialForm.twoVectorArguments
          (I := modelWithCornersSelf ℝ E) first second x) =
      form.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        s x first second := by
  rw [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates_normedSpace]
  let fields : Fin 2 → E → E := Fin.cases first (fun _ => second)
  have fields_differentiable : ∀ i, DifferentiableWithinAt ℝ (fields i) s x :=
    fun i => Fin.cases first_differentiable (fun _ => second_differentiable) i
  have formula := extDerivWithin_apply_vectorField form_differentiable
    fields_differentiable unique
  have tail_eq (z : E) : Fin.tail (fun i => fields i z) = fun _ : Fin 1 => second z := by
    funext i
    fin_cases i
    rfl
  have remove_eq (z : E) : Fin.removeNth 1 (fun i => fields i z) =
      fun _ : Fin 1 => first z := by
    funext i
    fin_cases i
    rfl
  have Ici_eq : Finset.Ici (0 : Fin 1) = Finset.univ := by
    ext j
    fin_cases j
    simp
  have fields_at (z : E) : (fun i => fields i z) =
      ManifoldDifferentialForm.twoVectorArguments
        (I := modelWithCornersSelf ℝ E) first second z := by
    funext i
    fin_cases i <;> rfl
  rw [← fields_at x]
  have fields_one (z : E) : fields 1 z = second z := rfl
  have vecCons_empty (z : E) (tail : Fin 0 → E) :
      Matrix.vecCons z tail = fun _ : Fin 1 => z := by
    funext i
    fin_cases i
    rfl
  simpa [fields, ManifoldDifferentialForm.twoVectorArguments, Fin.sum_univ_two,
    Fin.sum_univ_one, tail_eq, remove_eq, Ici_eq, fields_one, vecCons_empty,
    sub_eq_add_neg] using formula

/-- A smooth two-form certified to satisfy the local Cartan formula for a fixed smooth one-form.

The openness, point-membership, unique-differentiability, and smooth-field hypotheses remain
explicit so the interface is valid for manifolds with corners and within-set derivatives. -/
structure SmoothManifoldOneFormExteriorDerivativeCertificate
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1) where
  /-- Certified smooth degree-two form. -/
  derivative : SmoothManifoldDifferentialForm I M V coordinates 2
  /-- Exact Cartan formula on every admissible local set and pair of smooth tangent fields. -/
  cartan_formula : ∀ (s : Set M) (x : M), IsOpen s → x ∈ s → UniqueMDiffOn I s →
    ∀ first second,
      ManifoldTangentField.IsSmoothOn I s first →
      ManifoldTangentField.IsSmoothOn I s second →
      coordinates (derivative.toForm x
        (ManifoldDifferentialForm.twoVectorArguments first second x)) =
        form.toForm.oneFormCartanExpressionCoordinates coordinates s x first second

namespace SmoothManifoldOneFormExteriorDerivativeCertificate

/-- Two certificates for the same one-form agree on every admissible pair of local smooth fields. -/
theorem derivatives_agree_on_smoothFields
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (firstCertificate secondCertificate :
      SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second : (x : M) → TangentSpace I x)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second) :
    coordinates (firstCertificate.derivative.toForm x
      (ManifoldDifferentialForm.twoVectorArguments first second x)) =
    coordinates (secondCertificate.derivative.toForm x
      (ManifoldDifferentialForm.twoVectorArguments first second x)) := by
  rw [firstCertificate.cartan_formula s x open_s mem_s unique_s
      first second first_smooth second_smooth,
    secondCertificate.cartan_formula s x open_s mem_s unique_s
      first second first_smooth second_smooth]

/-- The smooth zero one-form has the smooth zero two-form as a concrete Cartan certificate. -/
noncomputable def zero (coordinates : V ≃L[ℝ] W) :
    SmoothManifoldOneFormExteriorDerivativeCertificate coordinates
      (SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V) coordinates 1) where
  derivative :=
    SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V) coordinates 2
  cartan_formula := by
    intro s x open_s mem_s unique_s first second first_smooth second_smooth
    simp [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates,
      SmoothManifoldDifferentialForm.zero, mfderivWithin_const]
    change 0 = (0 : W) - 0
    simp

end SmoothManifoldOneFormExteriorDerivativeCertificate

end YangMills.Mathematics
