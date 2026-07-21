/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundlePositiveCovariantExteriorDerivative

namespace YangMills.Geometry.AdjointBundlePositiveCovariantExteriorDerivative.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 1000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- The intrinsic positive-degree output is the exact quotient descent of the same candidate. -/
theorem exact_positive_covariant_exterior_descent
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm) :
    (PrincipalForm.covariantExteriorDerivativePositive IG IB IP smoothBundle connection n form
      exterior horizontal equivariant).toForm =
      PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm := rfl

/-- The curvature specialization is an exact smooth adjoint-valued three-form carrier. -/
theorem exact_curvature_covariant_exterior_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    (connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
      curvatureStructure curvatureExterior).toForm =
      PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (PrincipalForm.covariantExteriorCandidate connection 1
          (connection.curvatureForm exterior) curvatureExterior).toForm := rfl

/-- A disconnected intrinsic three-form cannot replace the same-chain `D_A F` descent. -/
theorem disconnected_curvature_covariant_exterior_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (changed : (connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
      curvatureStructure curvatureExterior).toForm ≠
      PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (PrincipalForm.covariantExteriorCandidate connection 1
          (connection.curvatureForm exterior) curvatureExterior).toForm) : False := changed rfl

end

end YangMills.Geometry.AdjointBundlePositiveCovariantExteriorDerivative.Probes
