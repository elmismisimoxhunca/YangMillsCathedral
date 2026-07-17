/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormRepresentativeIndependence

/-!
# Hostile probes for representative independence of principal two-forms
-/

namespace YangMills.Geometry.Probes

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

/-- Right translation cannot alter the projected tangent vector. -/
theorem rightTranslation_changes_projectionDifferential_blocked
    (p : P) (g : G) (v : TangentSpace IP p)
    (mismatch :
      mfderiv IP IB torsor.projection (torsor.rightAction p g)
          (principalRightTranslationDifferential smoothBundle p g v) ≠
        mfderiv IP IB torsor.projection p v) : False :=
  mismatch (principalBundleProjectionDifferential_rightTranslation_apply smoothBundle p g v)

/-- Right adjoint equivariance cannot produce a different adjoint quotient representative. -/
theorem equivariant_rightTranslation_changes_adjointQuotient_blocked
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (p : P) (g : G) (lifts : Fin 2 → TangentSpace IP p)
    (mismatch :
      AdjointBundle.mk torsor (torsor.rightAction p g)
          (form (torsor.rightAction p g)
            (fun i => principalRightTranslationDifferential smoothBundle p g (lifts i))) ≠
        AdjointBundle.mk torsor p (form p lifts)) : False :=
  mismatch (equivariant.mk_rightTranslation smoothBundle form p g lifts)

/-- Horizontal, equivariant values cannot depend on a right-related representative or replacement
lifts with identical projections. -/
theorem rightRelated_representativeOrLift_changes_adjointQuotient_blocked
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
          (principalRightTranslationDifferential smoothBundle p g (lifts i)))
    (mismatch :
      AdjointBundle.mk torsor (torsor.rightAction p g)
          (form (torsor.rightAction p g) translatedLifts) ≠
        AdjointBundle.mk torsor p (form p lifts)) : False :=
  mismatch (equivariant.mk_eq_of_rightTranslation_and_projection_eq smoothBundle form
    horizontal p g lifts translatedLifts sameProjection)

end

end YangMills.Geometry.Probes
