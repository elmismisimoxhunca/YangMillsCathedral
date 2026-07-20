/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.DirectAssociatedMaurerCartanPullbackSmooth
import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates
import YangMills.Mathematics.ManifoldOneFormExteriorDerivative
import YangMills.Mathematics.SmoothGradedLieBracketWedge

namespace YangMills.Geometry

/-!
# Maurer--Cartan structure candidate and invariant-field calculation

The universal left Maurer--Cartan form sends left-invariant fields back to their Lie-algebra
generators. Its Cartan expression on these canonical fields is exactly minus their bracket, fixing
the sign and the project self-wedge normalization. The associated gauge form is identified with the
exact pullback of this universal carrier, and `-1/2[α∧α]` is packaged as a smooth two-form candidate.

This file deliberately does **not** certify that the candidate is the exterior derivative of `α`.
The project's arbitrary-manifold exterior derivative is certificate-based; field-extension
tensoriality and arbitrary-smooth-map certificate pullback remain required before a full
Maurer--Cartan structure equation can be claimed.
-/

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Universal left Maurer--Cartan one-form, using exactly the project's left trivialization. -/
noncomputable def leftMaurerCartanForm :
    ManifoldDifferentialForm IG G (GroupLieAlgebra IG G) 1 := fun g =>
  ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace IG g)
    (GroupLieAlgebra IG G) (0 : Fin 1)
    (mfderiv IG IG (lieGroupLeftTranslation g⁻¹) g)

omit [IsTopologicalGroup G] [LieGroup IG ∞ G] in
@[simp] theorem leftMaurerCartanForm_evalOne (g : G) (w : TangentSpace IG g) :
    leftMaurerCartanForm (IG := IG) (G := G).evalOne g w =
      leftMaurerCartanApply g w := by
  simp [leftMaurerCartanForm, ManifoldDifferentialForm.evalOne,
    leftMaurerCartanApply]
  rfl

omit [IsTopologicalGroup G] in
/-- Left trivialization sends Mathlib's left-invariant vector field back to its defining Lie-algebra
value. -/
theorem leftMaurerCartanApply_mulInvariantVectorField
    [CompleteSpace EG] [ENat.LEInfty (minSmoothness ℝ 3)]
    (g : G) (v : GroupLieAlgebra IG G) :
    leftMaurerCartanApply g (mulInvariantVectorField v g) = v := by
  let forward : G → G := fun x => g * x
  let backward : G → G := fun x => g⁻¹ * x
  have hcomp := mfderiv_comp (I := IG) (I' := IG) (I'' := IG)
    (f := forward) (g := backward) (1 : G)
    ((lieGroupLeftTranslation_smooth (IG := IG) g⁻¹).mdifferentiableAt (by simp))
    ((lieGroupLeftTranslation_smooth (IG := IG) g).mdifferentiableAt (by simp))
  have hfun : backward ∘ forward = id := by
    funext x
    simp [backward, forward]
  rw [hfun, mfderiv_id] at hcomp
  have happ := congrArg (fun L => L v) hcomp
  change v = mfderiv IG IG backward (forward 1)
    (mfderiv IG IG forward 1 v) at happ
  change mfderiv IG IG backward g (mfderiv IG IG forward 1 v) = v
  rw [show forward 1 = g by simp [forward]] at happ
  exact happ.symm

omit [IsTopologicalGroup G] in
/-- The universal form sends the Lie bracket of two invariant fields to the exact Mathlib group
Lie-algebra bracket at every group point. -/
theorem leftMaurerCartanForm_mlieBracket_invariant
    [CompleteSpace EG] [ENat.LEInfty (minSmoothness ℝ 3)]
    (g : G) (v w : GroupLieAlgebra IG G) :
    (leftMaurerCartanForm (IG := IG) (G := G)).evalOne g
        (VectorField.mlieBracket IG (mulInvariantVectorField v)
          (mulInvariantVectorField w) g) = ⁅v, w⁆ := by
  have hfield := congrFun (mulInvariantVector_mlieBracket (I := IG) v w) g
  rw [← hfield, leftMaurerCartanForm_evalOne,
    leftMaurerCartanApply_mulInvariantVectorField]
  rfl

omit [IsTopologicalGroup G] in
/-- On the invariant fields that span each tangent space, the intrinsic Cartan expression is exactly
minus the Lie bracket. This is the checked universal Maurer--Cartan calculation; extending it to the
project's all-smooth-fields certificate is the remaining gap. -/
theorem leftMaurerCartanForm_cartan_invariant
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (g : G) (v w : GroupLieAlgebra IG G) :
    (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) Set.univ g
        (mulInvariantVectorField v) (mulInvariantVectorField w) =
      -(groupLieAlgebraModelEquiv IG) ⁅v, w⁆ := by
  let theta := leftMaurerCartanForm (IG := IG) (G := G)
  let coordinates := groupLieAlgebraModelEquiv (G := G) IG
  have eval_invariant (u : GroupLieAlgebra IG G) :
      (fun y => coordinates (theta y (fun _ => mulInvariantVectorField u y))) =
        (fun _ : G => coordinates u) := by
    funext y
    change coordinates (theta.evalOne y (mulInvariantVectorField u y)) = coordinates u
    rw [leftMaurerCartanForm_evalOne,
      leftMaurerCartanApply_mulInvariantVectorField]
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
  rw [eval_invariant w, eval_invariant v]
  simp only [mfderivWithin_const, zero_apply, map_zero, sub_zero, zero_sub]
  rw [VectorField.mlieBracketWithin_univ]
  have hbracket := leftMaurerCartanForm_mlieBracket_invariant
    (IG := IG) g v w
  change theta g (fun _ => VectorField.mlieBracket IG
    (mulInvariantVectorField v) (mulInvariantVectorField w) g) = ⁅v, w⁆ at hbracket
  rw [hbracket]

omit [IsTopologicalGroup G] in
/-- Generic exact self-wedge normalization for any Lie-algebra-valued one-form. -/
theorem selfWedge_apply
    {E₀ H₀ M₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [TopologicalSpace H₀] [TopologicalSpace M₀]
    {I₀ : ModelWithCorners ℝ E₀ H₀} [ChartedSpace H₀ M₀]
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (alpha : ManifoldDifferentialForm I₀ M₀ (GroupLieAlgebra IG G) 1)
    (x : M₀) (args : Fin 2 → TangentSpace I₀ x) :
    ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := I₀) (M := M₀) 1 alpha alpha x args =
      (2 : ℝ) • ⁅alpha.evalOne x (args 0), alpha.evalOne x (args 1)⁆ := by
  rw [ManifoldDifferentialForm.lieBracketWedgeOneMany_apply, Fin.sum_univ_two]
  have hzero : Fin.removeNth 0 args = fun _ : Fin 1 => args 1 := by
    funext i
    fin_cases i
    rfl
  have hremove : Fin.removeNth 1 args = fun _ : Fin 1 => args 0 := by
    funext i
    fin_cases i
    rfl
  rw [hzero, hremove]
  simp [ManifoldDifferentialForm.evalOne, lie_skew, two_smul]

omit [IsTopologicalGroup G] in
/-- The canonical candidate `-1/2[θ∧θ]` satisfies the exact Cartan formula on all invariant
fields, with no sign or normalization ambiguity. -/
theorem leftMaurerCartan_candidate_cartan_invariant
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (g : G) (v w : GroupLieAlgebra IG G) :
    (groupLieAlgebraModelEquiv IG)
        (((-1 / 2 : ℝ) •
          ManifoldDifferentialForm.lieBracketWedgeOneMany
            (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
            (leftMaurerCartanForm (IG := IG) (G := G))
            (leftMaurerCartanForm (IG := IG) (G := G))) g
          (ManifoldDifferentialForm.twoVectorArguments
            (mulInvariantVectorField v) (mulInvariantVectorField w) g)) =
      (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) Set.univ g
        (mulInvariantVectorField v) (mulInvariantVectorField w) := by
  rw [leftMaurerCartanForm_cartan_invariant]
  change (groupLieAlgebraModelEquiv IG) ((-1 / 2 : ℝ) •
    (ManifoldDifferentialForm.lieBracketWedgeOneMany
      (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
      (leftMaurerCartanForm (IG := IG) (G := G))
      (leftMaurerCartanForm (IG := IG) (G := G)) g
      (ManifoldDifferentialForm.twoVectorArguments
        (mulInvariantVectorField v) (mulInvariantVectorField w) g))) = _
  rw [map_smul, selfWedge_apply]
  change (-1 / 2 : ℝ) • (groupLieAlgebraModelEquiv IG)
    ((2 : ℝ) • ⁅(leftMaurerCartanForm (IG := IG) (G := G)).evalOne g
      (mulInvariantVectorField v g),
      (leftMaurerCartanForm (IG := IG) (G := G)).evalOne g
      (mulInvariantVectorField w g)⁆) = _
  rw [leftMaurerCartanForm_evalOne, leftMaurerCartanApply_mulInvariantVectorField,
    leftMaurerCartanForm_evalOne, leftMaurerCartanApply_mulInvariantVectorField,
    map_smul, smul_smul]
  norm_num

/-- The exact existing associated form is literally the pullback of the universal form. -/
theorem associated_eq_pullback (gauge : SmoothGaugeTransformation smoothBundle) :
    gauge.associatedMaurerCartanPullback =
      ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (leftMaurerCartanForm (IG := IG) (G := G)) := by
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  rw [show v = fun _ : Fin 1 => v 0 by funext i; fin_cases i; rfl]
  simp [ManifoldDifferentialForm.pullback,
    SmoothGaugeTransformation.associatedMaurerCartanPullback,
    leftMaurerCartanForm]
  rfl

/-- The exact self-wedge has the normalization required by `dα + 1/2[α∧α]`: on an
ordered pair it is twice the Lie bracket of the same exact `α` evaluations. -/
theorem associated_selfWedge_apply
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (v : Fin 2 → TangentSpace IP p) :
    ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback
        gauge.associatedMaurerCartanPullback p v =
      (2 : ℝ) • ⁅gauge.associatedMaurerCartanPullback.evalOne p (v 0),
        gauge.associatedMaurerCartanPullback.evalOne p (v 1)⁆ := by
  rw [ManifoldDifferentialForm.lieBracketWedgeOneMany_apply, Fin.sum_univ_two]
  have hzero : Fin.removeNth 0 v = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  have hremove : Fin.removeNth 1 v = fun _ : Fin 1 => v 0 := by
    funext i
    fin_cases i
    rfl
  rw [hzero, hremove]
  simp [ManifoldDifferentialForm.evalOne, lie_skew, two_smul]

/-- Smooth candidate for the exact exterior derivative of the existing `α`. Its carrier is
canonically and definitionally built from that same smooth form, rather than supplied independently. -/
noncomputable def associatedMaurerCartanDerivativeCandidate
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (gauge : SmoothGaugeTransformation smoothBundle) :
    SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 2 :=
  SmoothManifoldDifferentialForm.smul (-1 / 2 : ℝ)
    (SmoothManifoldDifferentialForm.lieBracketWedgeOneMany
      (I := IP) (M := P) (V := GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 1
      gauge.associatedMaurerCartanPullbackSmoothForm
      gauge.associatedMaurerCartanPullbackSmoothForm)

@[simp] theorem associatedMaurerCartanDerivativeCandidate_toForm
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanDerivativeCandidate gauge).toForm =
      (-1 / 2 : ℝ) •
        ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
          gauge.associatedMaurerCartanPullback
          gauge.associatedMaurerCartanPullback := by
  unfold associatedMaurerCartanDerivativeCandidate
  rw [SmoothManifoldDifferentialForm.smul_toForm,
    SmoothManifoldDifferentialForm.lieBracketWedgeOneMany_toForm]
  rfl

/-- The candidate already satisfies the desired equation as an exact equality of forms. What is
not yet checked is the certificate field asserting that this candidate is `dα`. -/
theorem associatedMaurerCartanDerivativeCandidate_add_half_selfWedge
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanDerivativeCandidate gauge).toForm + (1 / 2 : ℝ) •
      ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback
        gauge.associatedMaurerCartanPullback = 0 := by
  rw [associatedMaurerCartanDerivativeCandidate_toForm]
  module


end
end YangMills.Geometry
