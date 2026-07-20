/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupLeftTrivializedFieldDerivative

namespace YangMills.Mathematics.LieGroupLeftTrivializedFieldDerivative.Probes

open Set
open scoped Manifold ContDiff
open YangMills.Geometry

universe uE uH uG

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

omit [FiniteDimensional ℝ E] [IsTopologicalGroup G] in
/-- The left-invariant field retains the full `C∞` regularity of the group. -/
theorem exact_left_invariant_field_smooth (X : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G => (⟨g, mulInvariantVectorField X g⟩ : TangentBundle I G)) :=
  contMDiff_mulInvariantVectorField_top I X

omit [IsTopologicalGroup G] in
/-- The right-invariant field's left coefficient is the exact inverse-adjoint orbit. -/
theorem exact_right_field_coefficient (Y : GroupLieAlgebra I G) (g : G) :
    leftMaurerCartanForm (IG := I) (G := G) g
        (fun _ => mulRightInvariantVectorField I Y g) =
      inverseAdjointOrbit I Y g :=
  leftTrivialized_mulRightInvariantVectorField I Y g

omit [IsTopologicalGroup G] in
/-- The negative-bracket derivative follows only from the exact remaining commutation premise. -/
theorem exact_conditional_inverse_adjoint_derivative
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
            (fun _ => mulRightInvariantVectorField I Y g))) 1 X)) =
      -groupLieAlgebraModelEquiv I ⁅X, Y⁆ :=
  mfderiv_leftTrivialized_mulRightInvariant_identity_of_mlieBracket_eq_zero I X Y hcommute

omit [IsTopologicalGroup G] in
/-- A wrong sign is rejected once the exact commutation premise is supplied. -/
theorem mismatched_conditional_derivative_blocked
    (X Y : GroupLieAlgebra I G)
    (hcommute : VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 = 0)
    (wrong : (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) 1
          (fun _ => mulRightInvariantVectorField I Y 1)))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I
          (leftMaurerCartanForm (IG := I) (G := G) g
            (fun _ => mulRightInvariantVectorField I Y g))) 1 X)) ≠
      -groupLieAlgebraModelEquiv I ⁅X, Y⁆) : False :=
  wrong (mfderiv_leftTrivialized_mulRightInvariant_identity_of_mlieBracket_eq_zero
    I X Y hcommute)

omit [IsTopologicalGroup G] in
/-- For a nonzero bracket, the opposite positive sign is impossible. -/
theorem positive_sign_derivative_blocked
    (X Y : GroupLieAlgebra I G)
    (hcommute : VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 = 0)
    (nonzero : groupLieAlgebraModelEquiv I ⁅X, Y⁆ ≠ 0)
    (wrongPositive : (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I
        (leftMaurerCartanForm (IG := I) (G := G) 1
          (fun _ => mulRightInvariantVectorField I Y 1)))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I
          (leftMaurerCartanForm (IG := I) (G := G) g
            (fun _ => mulRightInvariantVectorField I Y g))) 1 X)) =
      groupLieAlgebraModelEquiv I ⁅X, Y⁆) : False := by
  apply nonzero
  have hneg : -groupLieAlgebraModelEquiv I ⁅X, Y⁆ =
      groupLieAlgebraModelEquiv I ⁅X, Y⁆ := by
    calc
      -groupLieAlgebraModelEquiv I ⁅X, Y⁆ =
        (NormedSpace.fromTangentSpace
          (groupLieAlgebraModelEquiv I
            (leftMaurerCartanForm (IG := I) (G := G) 1
              (fun _ => mulRightInvariantVectorField I Y 1)))
          (mfderiv I (modelWithCornersSelf ℝ E)
            (fun g => groupLieAlgebraModelEquiv I
              (leftMaurerCartanForm (IG := I) (G := G) g
                (fun _ => mulRightInvariantVectorField I Y g))) 1 X)) :=
      (mfderiv_leftTrivialized_mulRightInvariant_identity_of_mlieBracket_eq_zero
        I X Y hcommute).symm
      _ = groupLieAlgebraModelEquiv I ⁅X, Y⁆ := wrongPositive
  have htwo : (2 : ℝ) • groupLieAlgebraModelEquiv I ⁅X, Y⁆ = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp hneg
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end

end YangMills.Mathematics.LieGroupLeftTrivializedFieldDerivative.Probes
