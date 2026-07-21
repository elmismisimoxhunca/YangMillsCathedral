/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionIntrinsicBianchiFiniteDimensional

namespace YangMills.Geometry.PrincipalConnectionIntrinsicBianchiFiniteDimensional.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G] [LieGroup IG (minSmoothness ℝ 3) G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

omit [LieGroup IG (minSmoothness ℝ 3) G] in
/-- No caller-supplied structure certificate occurs in the finite-dimensional intrinsic carrier. -/
theorem exact_structure_free_intrinsic_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior curvatureExterior =
      connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
        (connection.curvatureStructureCertificate_finiteDimensional IG IB IP smoothBundle exterior)
        curvatureExterior := rfl

/-- The finite-dimensional intrinsic Bianchi identity requires no supplied structure witness. -/
theorem exact_structure_free_intrinsic_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior curvatureExterior =
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative_finiteDimensional_eq_zero exterior
    curvatureExterior

/-- A nonzero structure-free carrier contradicts the derived finite-dimensional Bianchi theorem. -/
theorem changed_structure_free_intrinsic_bianchi_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (hostile : connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior
      curvatureExterior ≠ AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3) : False :=
  hostile (connection.curvatureCovariantExteriorDerivative_finiteDimensional_eq_zero exterior
    curvatureExterior)

end

end YangMills.Geometry.PrincipalConnectionIntrinsicBianchiFiniteDimensional.Probes
