/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureStructureFiniteDimensional
import YangMills.Geometry.PrincipalConnectionIntrinsicBianchiZero

/-!
# Finite-dimensional intrinsic Bianchi identity without a supplied structure certificate

Finite-dimensional principal calculus derives curvature horizontality and right-adjoint
equivariance from the connection laws. This module therefore specializes the intrinsic `D_A F`
carrier and its Bianchi identity so callers supply only the same connection-indexed first exterior
data and a curvature-indexed ordinary exterior certificate. It still constructs neither exterior
certificate nor a connection.
-/

namespace YangMills.Geometry

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

namespace PrincipalConnectionData

/-- The intrinsic smooth `D_A F` carrier with curvature structure derived automatically from the
finite-dimensional connection calculus. -/
noncomputable def curvatureCovariantExteriorDerivative_finiteDimensional
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
    (connection.curvatureStructureCertificate_finiteDimensional IG IB IP smoothBundle exterior)
    curvatureExterior

omit [LieGroup IG (minSmoothness ℝ 3) G] in
/-- The finite-dimensional carrier is definitionally the earlier same-chain descent using the
derived structure certificate. -/
@[simp] theorem curvatureCovariantExteriorDerivative_finiteDimensional_eq
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior curvatureExterior =
      connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
        (connection.curvatureStructureCertificate_finiteDimensional IG IB IP smoothBundle exterior)
        curvatureExterior := rfl

/-- Finite-dimensional intrinsic Bianchi identity with no caller-supplied curvature-structure
certificate and no assumed zero/naturality bridge. -/
theorem curvatureCovariantExteriorDerivative_finiteDimensional_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior curvatureExterior =
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative_eq_zero exterior
    (connection.curvatureStructureCertificate_finiteDimensional IG IB IP smoothBundle exterior)
    curvatureExterior

end PrincipalConnectionData

end

end YangMills.Geometry
