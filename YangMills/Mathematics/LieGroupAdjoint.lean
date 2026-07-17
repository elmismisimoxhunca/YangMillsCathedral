/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# The adjoint action of a Lie group on its tangent Lie algebra

Mathlib supplies the tangent Lie algebra but no named group adjoint map in the pinned version. This
module defines it as the derivative at the identity of conjugation and proves its identity,
composition, and inverse laws.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]

/-- Conjugation by a group element. -/
def lieGroupConjugation (g : G) : G → G :=
  fun h => g * h * g⁻¹

/-- Conjugation is smooth in a smooth Lie group. -/
theorem lieGroupConjugation_smooth [LieGroup I ∞ G] (g : G) :
    ContMDiff I I ∞ (lieGroupConjugation g) := by
  exact (contMDiff_const.mul contMDiff_id).mul contMDiff_const

/-- The adjoint continuous linear map is the derivative of conjugation at the identity. -/
def lieGroupAdjoint [LieGroup I ∞ G] (g : G) :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  mfderiv I I (lieGroupConjugation g) 1

/-- The adjoint map of the identity is the identity linear map. -/
@[simp]
theorem lieGroupAdjoint_one [LieGroup I ∞ G] :
    lieGroupAdjoint I (1 : G) = ContinuousLinearMap.id ℝ (GroupLieAlgebra I G) := by
  have conjugation_one : lieGroupConjugation (1 : G) = id := by
    funext h
    simp [lieGroupConjugation]
  rw [lieGroupAdjoint, conjugation_one, mfderiv_id]

/-- Adjoint turns group multiplication into composition in the same order. -/
theorem lieGroupAdjoint_mul [LieGroup I ∞ G] (g h : G) :
    lieGroupAdjoint I (g * h) = (lieGroupAdjoint I g).comp (lieGroupAdjoint I h) := by
  have conjugation_mul :
      lieGroupConjugation (g * h) = lieGroupConjugation g ∘ lieGroupConjugation h := by
    funext x
    simp [lieGroupConjugation, Function.comp_apply]
    group
  have derivative_comp := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := lieGroupConjugation h) (g := lieGroupConjugation g) (1 : G)
    ((lieGroupConjugation_smooth I g).mdifferentiableAt (by simp))
    ((lieGroupConjugation_smooth I h).mdifferentiableAt (by simp))
  have conjugation_identity : lieGroupConjugation h 1 = 1 := by
    simp [lieGroupConjugation]
  rw [conjugation_identity] at derivative_comp
  rw [lieGroupAdjoint, conjugation_mul, derivative_comp]
  rfl

/-- The adjoint map of the inverse is a left inverse. -/
theorem lieGroupAdjoint_inv_apply [LieGroup I ∞ G]
    (g : G) (X : GroupLieAlgebra I G) :
    lieGroupAdjoint I g⁻¹ (lieGroupAdjoint I g X) = X := by
  have multiplication := lieGroupAdjoint_mul I g⁻¹ g
  rw [show g⁻¹ * g = 1 by simp, lieGroupAdjoint_one] at multiplication
  have evaluated := congrArg
    (fun map : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G => map X) multiplication
  simpa using evaluated.symm

/-- The adjoint map of the inverse is also a right inverse. -/
theorem lieGroupAdjoint_apply_inv [LieGroup I ∞ G]
    (g : G) (X : GroupLieAlgebra I G) :
    lieGroupAdjoint I g (lieGroupAdjoint I g⁻¹ X) = X := by
  have multiplication := lieGroupAdjoint_mul I g g⁻¹
  rw [show g * g⁻¹ = 1 by simp, lieGroupAdjoint_one] at multiplication
  have evaluated := congrArg
    (fun map : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G => map X) multiplication
  simpa using evaluated.symm

end

end YangMills.Mathematics
