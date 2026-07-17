/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureSmoothDescent

/-!
# Hostile probes for smooth certified-curvature descent
-/

namespace YangMills.Geometry.Probes

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

/-- Smoothness cannot fail for the exact curvature under its own indexed structural certificate. -/
theorem nonsmooth_exact_pointwiseBaseCurvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (failure : ¬AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (connection.pointwiseBaseCurvature exterior)) : False :=
  failure (connection.pointwiseBaseCurvature_isSmooth exterior certificate)

/-- Smooth packaging cannot replace the exact pointwise descended curvature carrier. -/
theorem replacement_smoothBaseCurvature_carrier_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (mismatch :
      (connection.smoothBaseCurvature exterior certificate).toForm ≠
        connection.pointwiseBaseCurvature exterior) : False :=
  mismatch (connection.smoothBaseCurvature_toForm exterior certificate)

/-- An unrelated principal two-form cannot silently become the carrier of the smooth certified
curvature package. -/
theorem unrelated_principalForm_smoothBaseCurvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate :
      PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (other : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (other_ne :
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) other ≠
        connection.pointwiseBaseCurvature exterior)
    (mistaken :
      (connection.smoothBaseCurvature exterior certificate).toForm =
        PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) other) : False :=
  other_ne (mistaken.symm.trans
    (connection.smoothBaseCurvature_toForm exterior certificate))

end

end YangMills.Geometry.Probes
