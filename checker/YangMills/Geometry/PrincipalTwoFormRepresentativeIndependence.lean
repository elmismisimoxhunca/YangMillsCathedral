/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormLiftIndependence
import YangMills.Geometry.AdjointBundle

/-!
# Representative independence of horizontal equivariant principal two-forms

Right translation preserves projected tangent vectors at the differential level. A right
adjoint-equivariant principal two-form therefore gives the same adjoint-quotient point at
right-related total-space representatives. Combined with horizontality, this remains true for any
other tangent lifts with the same projections at the translated representative.

This proves the quotient well-definedness ingredients. It does not yet construct or prove smoothness
of a descended base two-form.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- The differential of right translation preserves projection differentials. -/
theorem principalBundleProjectionDifferential_comp_rightTranslationDifferential
    (p : P) (g : G) :
    (mfderiv IP IB torsor.projection (torsor.rightAction p g)).comp
        (principalRightTranslationDifferential smoothBundle p g) =
      mfderiv IP IB torsor.projection p := by
  have rightMDiffAt :=
    (principalRightTranslation_smooth smoothBundle g p).mdifferentiableAt (by simp)
  have projectionMDiffAt :=
    (smoothBundle.projection_smooth (torsor.rightAction p g)).mdifferentiableAt (by simp)
  have chain := mfderiv_comp p projectionMDiffAt rightMDiffAt
  have comp_eq : torsor.projection ∘ principalRightTranslation torsor g = torsor.projection := by
    funext q
    exact torsor.projection_rightAction q g
  rw [comp_eq] at chain
  exact chain.symm

/-- Pointwise application of the projection differential is unchanged after right translation. -/
theorem principalBundleProjectionDifferential_rightTranslation_apply
    (p : P) (g : G) (v : TangentSpace IP p) :
    mfderiv IP IB torsor.projection (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g v) =
      mfderiv IP IB torsor.projection p v := by
  exact congrArg (fun f => f v)
    (principalBundleProjectionDifferential_comp_rightTranslationDifferential smoothBundle p g)

namespace PrincipalTwoForm.IsRightAdEquivariant

/-- Right-equivariant evaluation at right-related representatives defines the same actual adjoint
orbit-quotient point. -/
theorem mk_rightTranslation
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (p : P) (g : G) (lifts : Fin 2 → TangentSpace IP p) :
    AdjointBundle.mk torsor (torsor.rightAction p g)
        (form (torsor.rightAction p g)
          (fun i => principalRightTranslationDifferential smoothBundle p g (lifts i))) =
      AdjointBundle.mk torsor p (form p lifts) := by
  rw [equivariant g p lifts]
  exact AdjointBundle.mk_rightAction torsor p (form p lifts) g

/-- Horizontality and right equivariance together make the adjoint-quotient value independent of
both a right-related representative and any replacement lifts with the same projections there. -/
theorem mk_eq_of_rightTranslation_and_projection_eq
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (p : P) (g : G)
    (lifts : Fin 2 → TangentSpace IP p)
    (translatedLifts : Fin 2 → TangentSpace IP (torsor.rightAction p g))
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection (torsor.rightAction p g) (translatedLifts i) =
        mfderiv IP IB torsor.projection (torsor.rightAction p g)
          (principalRightTranslationDifferential smoothBundle p g (lifts i))) :
    AdjointBundle.mk torsor (torsor.rightAction p g)
        (form (torsor.rightAction p g) translatedLifts) =
      AdjointBundle.mk torsor p (form p lifts) := by
  have liftEq := horizontal.eq_of_projection_eq smoothBundle form
    (torsor.rightAction p g) translatedLifts
    (fun i => principalRightTranslationDifferential smoothBundle p g (lifts i)) sameProjection
  rw [liftEq]
  exact equivariant.mk_rightTranslation smoothBundle form p g lifts

end PrincipalTwoForm.IsRightAdEquivariant

end

end YangMills.Geometry
