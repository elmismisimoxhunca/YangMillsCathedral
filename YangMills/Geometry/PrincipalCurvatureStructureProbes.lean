/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureStructure

/-!
# Hostile probes for principal-curvature structure
-/

namespace YangMills.Geometry.Probes

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The zero two-form is a positive consistency check for the exact horizontal predicate. -/
theorem zero_principalTwoForm_horizontal :
    PrincipalTwoForm.IsHorizontal smoothBundle
      (0 : YangMills.Mathematics.ManifoldDifferentialForm IP P
        (GroupLieAlgebra IG G) 2) := by
  intro p v vertical
  rfl

/-- The zero two-form is also exactly right `Ad(g⁻¹)`-equivariant. -/
theorem zero_principalTwoForm_rightAdEquivariant :
    PrincipalTwoForm.IsRightAdEquivariant smoothBundle
      (0 : YangMills.Mathematics.ManifoldDifferentialForm IP P
        (GroupLieAlgebra IG G) 2) := by
  intro g p v
  simp

/-- A certified curvature cannot be nonzero on a tuple containing a projection-vertical vector. -/
theorem nonhorizontal_principalCurvature_blocked
    [FiniteDimensional ℝ EG]
    {connection : PrincipalConnectionData smoothBundle}
    {exterior : PrincipalConnectionExteriorDerivativeData connection}
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (p : P) (v : Fin 2 → TangentSpace IP p)
    (vertical : ∃ i, mfderiv IP IB torsor.projection p (v i) = 0)
    (nonzero : (connection.curvatureForm exterior).toForm p v ≠ 0) : False :=
  nonzero (certificate.horizontal p v vertical)

/-- A certified curvature cannot violate Freed's right-adjoint transformation law. -/
theorem nonequivariant_principalCurvature_blocked
    [FiniteDimensional ℝ EG]
    {connection : PrincipalConnectionData smoothBundle}
    {exterior : PrincipalConnectionExteriorDerivativeData connection}
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (g : G) (p : P) (v : Fin 2 → TangentSpace IP p)
    (mismatch :
      (connection.curvatureForm exterior).toForm (torsor.rightAction p g)
          (fun i => principalRightTranslationDifferential smoothBundle p g (v i)) ≠
        YangMills.Mathematics.lieGroupAdjoint IG g⁻¹
          ((connection.curvatureForm exterior).toForm p v)) : False :=
  mismatch (certificate.right_ad_equivariant g p v)

end

end YangMills.Geometry.Probes
