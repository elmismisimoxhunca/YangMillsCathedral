/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvaturePointwiseDescent
import YangMills.Geometry.PrincipalTwoFormSmoothDescent

/-!
# Smooth descent of certified principal curvature

The exact curvature derived from one principal connection and exterior-derivative datum descends to
a smooth adjoint-bundle-valued two-form when supplied with the structural certificate indexed by
that same curvature. No unrelated curvature or regularity witness is accepted.

This module packages a conditional construction. It does not construct a connection, an
exterior-derivative datum, or a structural certificate.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology

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
    [FiniteDimensional ℝ EG]

namespace PrincipalConnectionData

/-- The exact pointwise descended curvature is smooth. The structural certificate is indexed by the
same connection and exterior-derivative datum, so it cannot certify an unrelated principal form. -/
theorem pointwiseBaseCurvature_isSmooth
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (connection.pointwiseBaseCurvature exterior) := by
  rw [connection.pointwiseBaseCurvature_eq exterior]
  exact PrincipalTwoForm.selectedBaseForm_isSmooth smoothBundle
    (connection.curvatureForm exterior).toForm
    (connection.curvatureForm exterior).smooth
    certificate.horizontal certificate.right_ad_equivariant

/-- The smooth descended base curvature, retaining the exact pointwise curvature carrier. -/
noncomputable def smoothBaseCurvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle 2 where
  toForm := connection.pointwiseBaseCurvature exterior
  smooth := connection.pointwiseBaseCurvature_isSmooth exterior certificate

/-- Smooth packaging does not replace the exact connection-derived pointwise base curvature. -/
@[simp]
theorem smoothBaseCurvature_toForm
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    (connection.smoothBaseCurvature exterior certificate).toForm =
      connection.pointwiseBaseCurvature exterior :=
  rfl

/-- Unfolding the smooth package exposes descent of the exact derived principal curvature, not a
caller-supplied two-form. -/
theorem smoothBaseCurvature_toForm_eq_selected
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    (connection.smoothBaseCurvature exterior certificate).toForm =
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (connection.curvatureForm exterior).toForm :=
  rfl

end PrincipalConnectionData

end

end YangMills.Geometry
