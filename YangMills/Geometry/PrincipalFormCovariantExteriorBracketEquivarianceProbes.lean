/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormCovariantExteriorBracketEquivariance

/-!
# Hostile probes for covariant-bracket equivariance
-/

namespace YangMills.Geometry.PrincipalFormCovariantExteriorBracketEquivariance.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
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

/-- The exact bracket correction preserves right-adjoint equivariance in arbitrary degree. -/
theorem exact_bracket_equivariance
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm) :
    PrincipalForm.IsRightAdEquivariant smoothBundle
      (PrincipalForm.covariantExteriorBracket connection n form).toForm :=
  PrincipalForm.covariantExteriorBracket_isRightAdEquivariant
    connection n form equivariant

/-- A claimed failure of bracket-term equivariance contradicts the derived theorem. -/
theorem nonequivariant_bracket_blocked
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (wrong : ¬ PrincipalForm.IsRightAdEquivariant smoothBundle
      (PrincipalForm.covariantExteriorBracket connection n form).toForm) : False :=
  wrong (PrincipalForm.covariantExteriorBracket_isRightAdEquivariant
    connection n form equivariant)

end

end YangMills.Geometry.PrincipalFormCovariantExteriorBracketEquivariance.Probes
