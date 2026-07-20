/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupAdjoint
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph

/-!
# Lie-group adjoint preservation of the tangent Lie bracket

Inner conjugation is packaged as a smooth diffeomorphism. Its pushforward transports left-invariant
vector fields exactly, and Mathlib pullback naturality of `mlieBracket` proves that the project's
derivative-defined adjoint action preserves the intrinsic tangent Lie bracket.
-/

namespace YangMills.Mathematics

open Function
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]

/-- Packaging of inner conjugation as a smooth diffeomorphism. -/
def lieGroupConjugationDiffeomorph [LieGroup I ∞ G] (g : G) :
    G ≃ₘ^∞⟮I, I⟯ G where
  toEquiv :=
    { toFun := lieGroupConjugation g
      invFun := lieGroupConjugation g⁻¹
      left_inv := by
        intro x
        simp [lieGroupConjugation]
        group
      right_inv := by
        intro x
        simp [lieGroupConjugation]
        group }
  contMDiff_toFun := lieGroupConjugation_smooth I g
  contMDiff_invFun := lieGroupConjugation_smooth I g⁻¹

@[simp]
theorem lieGroupConjugationDiffeomorph_apply [LieGroup I ∞ G] (g x : G) :
    lieGroupConjugationDiffeomorph I g x = lieGroupConjugation g x := rfl

@[simp]
theorem lieGroupConjugationDiffeomorph_symm_apply [LieGroup I ∞ G] (g x : G) :
    (lieGroupConjugationDiffeomorph I g).symm x = lieGroupConjugation g⁻¹ x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward by conjugation of a left-invariant field is the left-invariant field
of the adjoint-transformed identity value. -/
theorem lieGroupConjugation_pushforward_mulInvariantVectorField
    [LieGroup I ∞ G]
    (g : G) (X : GroupLieAlgebra I G) :
    Diffeomorph.pushforwardField (lieGroupConjugationDiffeomorph I g)
        (mulInvariantVectorField X) =
      mulInvariantVectorField (lieGroupAdjoint I g X) := by
  funext y
  unfold Diffeomorph.pushforwardField mulInvariantVectorField lieGroupAdjoint
  simp only [lieGroupConjugationDiffeomorph_symm_apply]
  let z := lieGroupConjugation g⁻¹ y
  change (mfderiv I I (lieGroupConjugation g) z)
      ((mfderiv I I (fun x : G => z * x) 1) X) =
    (mfderiv I I (fun x : G => y * x) 1)
      ((mfderiv I I (lieGroupConjugation g) 1) X)
  have hz : lieGroupConjugation g z = y := by
    simp [z, lieGroupConjugation]
    group
  have hfun :
      lieGroupConjugation g ∘ (fun x => z * x) =
        (fun x => y * x) ∘ lieGroupConjugation g := by
    funext x
    change lieGroupConjugation g (z * x) = y * lieGroupConjugation g x
    rw [← hz]
    simp only [lieGroupConjugation]
    group
  have hsmoothLeftZ : ContMDiff I I ∞ (fun x : G => z * x) :=
    contMDiff_const.mul contMDiff_id
  have hsmoothLeftY : ContMDiff I I ∞ (fun x : G => y * x) :=
    contMDiff_const.mul contMDiff_id
  have hleft := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := fun x : G => z * x) (g := lieGroupConjugation g) (1 : G)
    ((lieGroupConjugation_smooth I g).mdifferentiableAt (by simp))
    (hsmoothLeftZ.mdifferentiableAt (by simp))
  have hright := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := lieGroupConjugation g) (g := fun x : G => y * x) (1 : G)
    (hsmoothLeftY.mdifferentiableAt (by simp))
    ((lieGroupConjugation_smooth I g).mdifferentiableAt (by simp))
  rw [mfderiv_congr (x := (1 : G)) hfun] at hleft
  have hmaps := hleft.symm.trans hright
  have hone : lieGroupConjugation g (1 : G) = 1 := by
    simp [lieGroupConjugation]
  rw [mul_one z, hone] at hmaps
  change ((mfderiv I I (lieGroupConjugation g) z).comp
      (mfderiv I I (fun x : G => z * x) 1)) X =
    ((mfderiv I I (fun x : G => y * x) 1).comp
      (mfderiv I I (lieGroupConjugation g) 1)) X
  exact congrArg (fun L => L X) hmaps

set_option backward.isDefEq.respectTransparency false in
/-- The project adjoint map preserves Mathlib's tangent Lie bracket. -/
theorem lieGroupAdjoint_lieBracket
    [LieGroup I ∞ G] [LieGroup I (minSmoothness ℝ 3) G]
    [IsManifold I (minSmoothness ℝ 2) G] [CompleteSpace E]
    (g : G) (X Y : GroupLieAlgebra I G) :
    lieGroupAdjoint I g ⁅X, Y⁆ =
      ⁅lieGroupAdjoint I g X, lieGroupAdjoint I g Y⁆ := by
  let e := lieGroupConjugationDiffeomorph I g
  have hXpull :
      VectorField.mpullback I I e
          (mulInvariantVectorField (lieGroupAdjoint I g X)) =
        mulInvariantVectorField X := by
    rw [← lieGroupConjugation_pushforward_mulInvariantVectorField I g X]
    exact Diffeomorph.mpullback_pushforwardField e (mulInvariantVectorField X)
  have hYpull :
      VectorField.mpullback I I e
          (mulInvariantVectorField (lieGroupAdjoint I g Y)) =
        mulInvariantVectorField Y := by
    rw [← lieGroupConjugation_pushforward_mulInvariantVectorField I g Y]
    exact Diffeomorph.mpullback_pushforwardField e (mulInvariantVectorField Y)
  have htransport := VectorField.mpullback_mlieBracket
    (I := I) (I' := I) (n := minSmoothness ℝ 3) (f := (e : G → G))
    (V := mulInvariantVectorField (lieGroupAdjoint I g X))
    (W := mulInvariantVectorField (lieGroupAdjoint I g Y))
    (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField (lieGroupAdjoint I g X))
    (mdifferentiableAt_mulInvariantVectorField (lieGroupAdjoint I g Y))
    (e.contMDiff.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact (show (↑(3 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).contMDiffAt
    (minSmoothness_monotone (by norm_cast))
  rw [hXpull, hYpull] at htransport
  have hforward := (Diffeomorph.isInvertible_mfderiv e (1 : G)).inverse_apply_eq.mp htransport
  have he_one : e (1 : G) = 1 := by
    change lieGroupConjugation g 1 = 1
    simp [lieGroupConjugation]
  have he_fun : (e : G → G) = lieGroupConjugation g := rfl
  rw [he_one, he_fun] at hforward
  change (mfderiv I I (lieGroupConjugation g) 1)
      (VectorField.mlieBracket I (mulInvariantVectorField X)
        (mulInvariantVectorField Y) 1) =
    VectorField.mlieBracket I
      (mulInvariantVectorField ((mfderiv I I (lieGroupConjugation g) 1) X))
      (mulInvariantVectorField ((mfderiv I I (lieGroupConjugation g) 1) Y)) 1
  exact hforward.symm

end

end YangMills.Mathematics
