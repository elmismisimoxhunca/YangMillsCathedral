/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFundamentalVectorField

/-!
# Hostile probes for smooth fundamental vector fields
-/

namespace YangMills.Geometry.PrincipalFundamentalVectorField.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The field is pointwise the exact existing infinitesimal orbit vector. -/
theorem exact_fundamental_field_value
    (X : GroupLieAlgebra IG G) (p : P) :
    principalFundamentalVectorField (smoothBundle := smoothBundle) X p =
      principalFundamentalVector smoothBundle p X :=
  rfl

/-- The global tangent-bundle-valued field is genuinely smooth. -/
theorem exact_fundamental_field_smooth
    (X : GroupLieAlgebra IG G) :
    ContMDiff IP (IP.tangent) ∞
      (fun p : P => (⟨p, principalFundamentalVectorField
        (smoothBundle := smoothBundle) X p⟩ : TangentBundle IP P)) :=
  principalFundamentalVectorField_contMDiff X

/-- Every field value is vertical for the exact projection. -/
theorem exact_fundamental_field_vertical
    (X : GroupLieAlgebra IG G) (p : P) :
    mfderiv IP IB torsor.projection p
      (principalFundamentalVectorField (smoothBundle := smoothBundle) X p) = 0 :=
  principalFundamentalVectorField_projection_eq_zero X p

/-- A smooth identity-based group curve with velocity `X` gives the exact fundamental velocity. -/
theorem exact_right_action_curve_velocity
    (p : P) (X : GroupLieAlgebra IG G) (curve : ℝ → G)
    (curve_zero : curve 0 = 1)
    (curve_smooth : ContMDiffAt (modelWithCornersSelf ℝ ℝ) IG ∞ curve 0)
    (curve_velocity : mfderiv (modelWithCornersSelf ℝ ℝ) IG curve 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) = X) :
    mfderiv (modelWithCornersSelf ℝ ℝ) IP
      (fun t => torsor.rightAction p (curve t)) 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) =
        principalFundamentalVector smoothBundle p X :=
  principalRightActionCurve_mfderiv p X curve curve_zero curve_smooth curve_velocity

/-- Finite right-adjoint equivariance remains exact along every group curve. -/
theorem exact_equivariance_along_curve
    {k : ℕ} (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) k)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form)
    (p : P) (vectors : Fin k → TangentSpace IP p) (curve : ℝ → G) (t : ℝ) :
    form (torsor.rightAction p (curve t))
        (fun i => principalRightTranslationDifferential smoothBundle p (curve t) (vectors i)) =
      lieGroupAdjoint IG (curve t)⁻¹ (form p vectors) :=
  PrincipalForm.rightAdEquivariant_along_curve form equivariant p vectors curve t

/-- A changed right-action curve velocity is rejected. -/
theorem mismatched_right_action_curve_velocity_blocked
    (p : P) (X : GroupLieAlgebra IG G) (curve : ℝ → G)
    (curve_zero : curve 0 = 1)
    (curve_smooth : ContMDiffAt (modelWithCornersSelf ℝ ℝ) IG ∞ curve 0)
    (curve_velocity : mfderiv (modelWithCornersSelf ℝ ℝ) IG curve 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) = X)
    (wrong : mfderiv (modelWithCornersSelf ℝ ℝ) IP
      (fun t => torsor.rightAction p (curve t)) 0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) ≠
        principalFundamentalVector smoothBundle p X) : False :=
  wrong (principalRightActionCurve_mfderiv p X curve curve_zero curve_smooth curve_velocity)

/-- A changed field value is rejected definitionally. -/
theorem mismatched_fundamental_field_blocked
    (X : GroupLieAlgebra IG G) (p : P)
    (wrong : principalFundamentalVectorField (smoothBundle := smoothBundle) X p ≠
      principalFundamentalVector smoothBundle p X) : False :=
  wrong rfl

end

end YangMills.Geometry.PrincipalFundamentalVectorField.Probes
