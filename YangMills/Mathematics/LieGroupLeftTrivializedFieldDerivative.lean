/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.UniversalMaurerCartanExteriorDerivative
import YangMills.Mathematics.LieGroupRightInvariantField

/-!
# Derivative of a left-trivialized tangent field

The universal Maurer--Cartan certificate computes the identity derivative of a smooth tangent
field's left-trivialized coefficient in terms of its manifold Lie bracket with a left-invariant
field. For the exact right-invariant field, this yields the expected negative adjoint-bracket formula
conditionally on the one still-missing mixed-derivative theorem that left- and right-invariant
fields commute. No commutation fact or infinitesimal adjoint formula is assumed unconditionally.
-/

namespace YangMills.Mathematics

open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Geometry

universe uE uH uG

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

omit [IsTopologicalGroup G] in
/-- Derivative at the identity of a vector field's left-trivialized coefficient. -/
theorem mfderiv_leftTrivializedCoefficient_identity
    (X : GroupLieAlgebra I G)
    (V : (g : G) → TangentSpace I g)
    (hV : ContMDiff I I.tangent ∞
      (fun g : G => (⟨g, V g⟩ : TangentBundle I G))) :
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) 1 (fun _ => V 1)))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I
          (leftMaurerCartanForm (IG := I) (G := G) g (fun _ => V g)))
        1 X)) =
      groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) 1
          (fun _ => VectorField.mlieBracket I (mulInvariantVectorField X) V 1)) -
      groupLieAlgebraModelEquiv I
        ⁅X, leftMaurerCartanForm (IG := I) (G := G) 1 (fun _ => V 1)⁆ := by
  let first := mulInvariantVectorField (I := I) X
  have hfirst : ManifoldTangentField.IsSmoothOn I Set.univ first :=
    (contMDiff_mulInvariantVectorField_top I X).contMDiffOn
  have hV' : ManifoldTangentField.IsSmoothOn I Set.univ V := hV.contMDiffOn
  have hcartan :=
    (leftMaurerCartanExteriorDerivativeCertificate (IG := I) (G := G)).cartan_formula
      Set.univ (1 : G) isOpen_univ (Set.mem_univ 1) uniqueMDiffOn_univ
      first V hfirst hV'
  rw [leftMaurerCartanExteriorDerivativeCertificate_derivative,
    leftMaurerCartanExteriorDerivative_toForm] at hcartan
  rw [ManifoldDifferentialForm.oneFormCartanExpressionCoordinates] at hcartan
  simp only [mfderivWithin_univ, VectorField.mlieBracketWithin_univ] at hcartan
  rw [leftMaurerCartanSmoothForm_toForm] at hcartan
  have hconst :
      (fun y => groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) y (fun _ => first y))) =
      (fun _ : G => groupLieAlgebraModelEquiv I X) := by
    funext y
    rw [show leftMaurerCartanForm (IG := I) (G := G) y (fun _ => first y) =
      leftMaurerCartanForm.evalOne y (first y) by rfl,
      leftMaurerCartanForm_evalOne,
      leftMaurerCartanApply_mulInvariantVectorField]
  rw [hconst] at hcartan
  simp only [mfderiv_const, zero_apply, map_zero, sub_zero] at hcartan
  change (groupLieAlgebraModelEquiv I) ((-1 / 2 : ℝ) •
      (ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra I G) (I := I) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm 1
        (ManifoldDifferentialForm.twoVectorArguments first V 1))) = _ at hcartan
  rw [map_smul, selfWedge_apply] at hcartan
  change (-1 / 2 : ℝ) • (groupLieAlgebraModelEquiv I)
      ((2 : ℝ) •
        ⁅leftMaurerCartanForm.evalOne 1 (first 1),
          leftMaurerCartanForm.evalOne 1 (V 1)⁆) = _ at hcartan
  rw [leftMaurerCartanForm_evalOne,
    leftMaurerCartanApply_mulInvariantVectorField,
    leftMaurerCartanForm_evalOne, map_smul, smul_smul] at hcartan
  norm_num at hcartan
  have hfirstOne : first 1 = X := by
    change mfderiv I I (fun x : G => 1 * x) 1 X = X
    rw [show (fun x : G => 1 * x) = id by funext x; simp, mfderiv_id]
    exact ContinuousLinearMap.id_apply X
  rw [hfirstOne] at hcartan
  dsimp only [first] at hcartan
  have hVone : leftMaurerCartanForm (IG := I) (G := G) 1 (fun _ => V 1) =
      leftMaurerCartanApply 1 (V 1) := by
    change leftMaurerCartanForm.evalOne 1 (V 1) = _
    exact leftMaurerCartanForm_evalOne 1 (V 1)
  rw [eq_sub_iff_add_eq] at hcartan ⊢
  conv_lhs =>
    rhs
    rw [hVone]
  rw [← hcartan]
  abel

omit [IsTopologicalGroup G] in
/-- The left-trivialized coefficient of the constructed right-invariant field is exactly the
inverse-adjoint orbit. -/
theorem leftTrivialized_mulRightInvariantVectorField
    (Y : GroupLieAlgebra I G) (g : G) :
    leftMaurerCartanForm (IG := I) (G := G) g
        (fun _ => mulRightInvariantVectorField I Y g) =
      inverseAdjointOrbit I Y g := by
  change leftMaurerCartanForm.evalOne g (mulRightInvariantVectorField I Y g) = _
  rw [leftMaurerCartanForm_evalOne,
    mulRightInvariantVectorField_eq_mulInvariant_adjoint_inv,
    leftMaurerCartanApply_mulInvariantVectorField]
  rfl

omit [IsTopologicalGroup G] in
/-- Conditional right-invariant specialization: once commutation with the left-invariant field is
available, the derivative of its exact left-trivialized coefficient is the negative bracket. -/
theorem mfderiv_leftTrivialized_mulRightInvariant_identity_of_mlieBracket_eq_zero
    (X Y : GroupLieAlgebra I G)
    (hcommute : VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 = 0) :
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) 1
          (fun _ => mulRightInvariantVectorField I Y 1)))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I
          (leftMaurerCartanForm (IG := I) (G := G) g
            (fun _ => mulRightInvariantVectorField I Y g)))
        1 X)) =
      -groupLieAlgebraModelEquiv I ⁅X, Y⁆ := by
  let V := mulRightInvariantVectorField I Y
  have h := mfderiv_leftTrivializedCoefficient_identity I X V
    (contMDiff_mulRightInvariantVectorField I Y)
  have hzero : leftMaurerCartanForm (IG := I) (G := G) (1 : G)
      (fun _ => (0 : TangentSpace I (1 : G))) = 0 := by
    simp [leftMaurerCartanForm]
  have hcommute' : VectorField.mlieBracket I (mulInvariantVectorField X) V 1 = 0 :=
    hcommute
  rw [hcommute', hzero, map_zero, zero_sub] at h
  have hrightOne : mulRightInvariantVectorField I Y 1 = Y := by
    unfold mulRightInvariantVectorField
    rw [show (fun h : G => h * 1) = id by funext h; simp, mfderiv_id]
    exact ContinuousLinearMap.id_apply Y
  have hleftOne : mulInvariantVectorField Y 1 = Y := by
    unfold mulInvariantVectorField
    rw [show (fun h : G => 1 * h) = id by funext h; simp, mfderiv_id]
    exact ContinuousLinearMap.id_apply Y
  have hvalue : leftMaurerCartanForm (IG := I) (G := G) 1 (fun _ => V 1) = Y := by
    change leftMaurerCartanForm.evalOne 1 (mulRightInvariantVectorField I Y 1) = Y
    rw [hrightOne, ← hleftOne, leftMaurerCartanForm_evalOne,
      leftMaurerCartanApply_mulInvariantVectorField]
    exact hleftOne.symm
  change (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) 1 (fun _ => V 1)))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I
          (leftMaurerCartanForm (IG := I) (G := G) g (fun _ => V g)))
        1 X)) = _
  conv_rhs =>
    rhs
    rw [← hvalue]
  exact h

end
end YangMills.Mathematics
