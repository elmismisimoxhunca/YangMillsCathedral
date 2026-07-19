/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormExteriorDerivative

/-!
# Positive-degree Cartan certificates on manifolds

Pinned Mathlib supplies the general Cartan formula for `extDerivWithin` on normed spaces but no
global exterior derivative for differential forms on arbitrary manifolds. This module mirrors
Mathlib's exact triangular indexing and signs to define an intrinsic coordinate-valued Cartan
expression for degrees `(n+1) → (n+2)`, proves normed-space compatibility, and packages a smooth
manifold certificate.

The certificate remains supplied data until existence, chart independence, and sufficient local
smooth-field extension are proved. It does not identify arbitrary certificates into a canonical
global operator, establish `d² = 0`, prove graded Leibniz, or prove Bianchi. The `n = 1` alias is the
exact two-form-to-three-form surface needed by later curvature work.
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

/-- Coordinate-valued positive-degree Cartan expression, with the exact indexing and leading
subtraction used by Mathlib's `extDerivWithin_apply_vectorField`. -/
noncomputable def ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : ManifoldDifferentialForm I M V (n + 1))
    (s : Set M) (x : M)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y) : W :=
  (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (NormedSpace.fromTangentSpace
        (coordinates (form x (i.removeNth (fun k => fields k x)))))
        (mfderivWithin I (modelWithCornersSelf ℝ W)
          (fun y => coordinates (form y (i.removeNth (fun k => fields k y))))
          s x (fields i x))) -
    ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, (-1 : ℤ) ^ (i + j : ℕ) •
      coordinates (form x (Matrix.vecCons
        (VectorField.mlieBracketWithin I (fields i.castSucc) (fields j.succ) s x)
        (j.removeNth <| i.castSucc.removeNth (fun k => fields k x))))

/-- In normed-space coordinates, the intrinsic expression is definitionally Mathlib's
`fderivWithin`/`lieBracketWithin` expression. -/
theorem ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_normedSpace
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
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k x))) := by
  simp only [ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates,
    NormedSpaceDifferentialForm.toManifoldForm, mfderivWithin_eq_fderivWithin,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    ContinuousLinearEquiv.refl_apply]
  rfl

/-- Mathlib's general positive-degree local exterior derivative satisfies the exact intrinsic
coordinate Cartan expression. -/
theorem NormedSpaceDifferentialForm.extDerivWithin_eq_positiveDegreeCartanExpression
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
        n s x fields := by
  rw [ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates_normedSpace]
  exact extDerivWithin_apply_vectorField form_differentiable fields_differentiable unique

/-- A smooth `(n+2)`-form certified to satisfy the general local Cartan formula for one fixed
smooth `(n+1)`-form. All within-set hypotheses remain explicit for manifolds with corners. -/
structure SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1)) where
  /-- Certified smooth output of degree `n+2`. -/
  derivative : SmoothManifoldDifferentialForm I M V coordinates (n + 2)
  /-- Exact positive-degree Cartan formula on every admissible local set and smooth field tuple. -/
  cartan_formula : ∀ (s : Set M) (x : M), IsOpen s → x ∈ s → UniqueMDiffOn I s →
    ∀ fields : Fin (n + 2) → (y : M) → TangentSpace I y,
      (∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) →
      coordinates (derivative.toForm x (fun i => fields i x)) =
        form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s x fields

/-- Degree-two-to-three specialization needed to type the ordinary derivative of curvature. -/
abbrev SmoothManifoldTwoFormExteriorDerivativeCertificate
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 2) :=
  SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 1 form

namespace SmoothManifoldPositiveDegreeExteriorDerivativeCertificate

/-- Certificates for the same positive-degree form agree on every admissible smooth field tuple. -/
theorem derivatives_agree_on_smoothFields
    {coordinates : V ≃L[ℝ] W} {n : ℕ}
    {form : SmoothManifoldDifferentialForm I M V coordinates (n + 1)}
    (firstCertificate secondCertificate :
      SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    coordinates (firstCertificate.derivative.toForm x (fun i => fields i x)) =
      coordinates (secondCertificate.derivative.toForm x (fun i => fields i x)) := by
  rw [firstCertificate.cartan_formula s x open_s mem_s unique_s fields fields_smooth,
    secondCertificate.cartan_formula s x open_s mem_s unique_s fields fields_smooth]

/-- The smooth zero `(n+1)`-form has the smooth zero `(n+2)`-form as a concrete certificate. -/
noncomputable def zero (coordinates : V ≃L[ℝ] W) (n : ℕ) :
    SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n
      (SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V)
        coordinates (n + 1)) where
  derivative :=
    SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V)
      coordinates (n + 2)
  cartan_formula := by
    intro s x open_s mem_s unique_s fields fields_smooth
    rw [show ((SmoothManifoldDifferentialForm.zero
      (I := I) (M := M) (V := V) coordinates (n + 2)).toForm x)
        (fun i => fields i x) = 0 by rfl, map_zero]
    unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
    have first_sum_zero :
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (NormedSpace.fromTangentSpace
            (coordinates (((SmoothManifoldDifferentialForm.zero
              (I := I) (M := M) (V := V) coordinates (n + 1)).toForm x)
                (i.removeNth (fun k => fields k x)))))
          (mfderivWithin I (modelWithCornersSelf ℝ W)
            (fun y => coordinates (((SmoothManifoldDifferentialForm.zero
              (I := I) (M := M) (V := V) coordinates (n + 1)).toForm y)
                (i.removeNth (fun k => fields k y)))) s x (fields i x))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have zero_coefficient :
          (fun y => coordinates (((SmoothManifoldDifferentialForm.zero
            (I := I) (M := M) (V := V) coordinates (n + 1)).toForm y)
              (i.removeNth (fun k => fields k y)))) = (fun _ : M => (0 : W)) := by
        funext y
        rw [show (((SmoothManifoldDifferentialForm.zero
          (I := I) (M := M) (V := V) coordinates (n + 1)).toForm y)
            (i.removeNth (fun k => fields k y))) = 0 by rfl, map_zero]
      rw [show (((SmoothManifoldDifferentialForm.zero
        (I := I) (M := M) (V := V) coordinates (n + 1)).toForm x)
          (i.removeNth (fun k => fields k x))) = 0 by rfl, map_zero]
      rw [zero_coefficient, mfderivWithin_const]
      simp
    rw [first_sum_zero, zero_sub, eq_comm, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [show (((SmoothManifoldDifferentialForm.zero
      (I := I) (M := M) (V := V) coordinates (n + 1)).toForm x)
        (Matrix.vecCons (VectorField.mlieBracketWithin I
          (fields i.castSucc) (fields j.succ) s x)
          (j.removeNth (i.castSucc.removeNth (fun k => fields k x))))) = 0 by rfl,
      map_zero, smul_zero]

end SmoothManifoldPositiveDegreeExteriorDerivativeCertificate

end YangMills.Mathematics
