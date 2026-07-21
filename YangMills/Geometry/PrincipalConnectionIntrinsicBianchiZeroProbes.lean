/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionIntrinsicBianchiZero

namespace YangMills.Geometry.PrincipalConnectionIntrinsicBianchiZero.Probes

open scoped Manifold ContDiff Bundle Topology
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

omit [FiniteDimensional ℝ EB] [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The same-chain principal candidate vanishes at every centered inverse chart. -/
theorem exact_centered_principal_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (p : P) :
    (PrincipalForm.covariantExteriorCandidate connection 1
      (connection.curvatureForm exterior) curvatureExterior).toForm.inExtChartAt
        (groupLieAlgebraModelEquiv IG) 3 p ((extChartAt IP p) p) = 0 :=
  connection.curvatureCovariantExteriorCandidate_inExtChartAt_center_eq_zero
    exterior curvatureExterior p

omit [FiniteDimensional ℝ EB] in
/-- Centered chart cancellation recovers global principal-total-space Bianchi zero. -/
theorem exact_global_principal_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    (PrincipalForm.covariantExteriorCandidate connection 1
      (connection.curvatureForm exterior) curvatureExterior).toForm = 0 :=
  connection.curvatureCovariantExteriorCandidate_toForm_eq_zero exterior curvatureExterior

/-- The intrinsic descended carrier is exactly the canonical smooth zero form. -/
theorem exact_intrinsic_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
        curvatureStructure curvatureExterior =
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative_eq_zero exterior curvatureStructure
    curvatureExterior

/-- A nonzero or disconnected descended Bianchi carrier contradicts the derived intrinsic identity. -/
theorem changed_intrinsic_bianchi_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (changed :
      (connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
        curvatureStructure curvatureExterior).toForm ≠
        (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm) : False :=
  changed (connection.curvatureCovariantExteriorDerivative_toForm_eq_zero exterior
    curvatureStructure curvatureExterior)

end

end YangMills.Geometry.PrincipalConnectionIntrinsicBianchiZero.Probes
