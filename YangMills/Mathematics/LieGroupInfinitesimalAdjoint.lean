/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInvariantFieldCommutation
import YangMills.Mathematics.LieGroupLeftTrivializedFieldDerivative

/-!
# Infinitesimal inverse adjoint action

Left- and right-invariant commutation, combined with the certified universal Maurer--Cartan equation,
proves the exact negative-bracket derivative of the inverse-adjoint orbit at the identity. The
statement uses the project's derivative and model-coordinate carriers and introduces no exponential
map or one-parameter subgroup.
-/

namespace YangMills.Mathematics

open Set Bundle
open scoped Manifold ContDiff
open YangMills.Geometry

universe uE uH uG

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

/-- At the identity, differentiating `g ↦ Ad(g⁻¹)Y` in direction `X` gives `-[X,Y]` in exact
model coordinates. -/
theorem mfderiv_inverseAdjointOrbit_identity (X Y : GroupLieAlgebra I G) :
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y 1))
      (mfderiv I (modelWithCornersSelf ℝ E)
        (fun g => groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y g)) 1 X)) =
      -groupLieAlgebraModelEquiv I ⁅X, Y⁆ := by
  have hcommute := mlieBracket_mulInvariant_mulRightInvariant_identity I X Y
  have h := mfderiv_leftTrivialized_mulRightInvariant_identity_of_mlieBracket_eq_zero
    I X Y hcommute
  have hfun : (fun g => groupLieAlgebraModelEquiv I
      (leftMaurerCartanForm (IG := I) (G := G) g
        (fun _ => mulRightInvariantVectorField I Y g))) =
      (fun g => groupLieAlgebraModelEquiv I (inverseAdjointOrbit I Y g)) := by
    funext g
    rw [leftTrivialized_mulRightInvariantVectorField I Y g]
  have hbase : leftMaurerCartanForm (IG := I) (G := G) 1
      (fun _ => mulRightInvariantVectorField I Y 1) = inverseAdjointOrbit I Y 1 :=
    leftTrivialized_mulRightInvariantVectorField I Y 1
  rw [hfun] at h
  rw [hbase] at h
  exact h

end

end YangMills.Mathematics
