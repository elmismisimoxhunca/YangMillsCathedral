/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCartanTriangularDischarge
import YangMills.Geometry.PrincipalFormCovariantExteriorEquivariance
import YangMills.Geometry.PrincipalFormSmoothDescent
import YangMills.Geometry.PrincipalCurvatureStructure

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 2000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
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

namespace PrincipalForm

/-- The intrinsic positive-degree adjoint-bundle covariant exterior derivative obtained by
smoothly descending the exact principal candidate `dω + [Θ ∧ ω]`. -/
noncomputable def covariantExteriorDerivativePositive
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle (n + 2) :=
  selectedBaseFormSmooth smoothBundle
    (covariantExteriorCandidate connection n form exterior).toForm
    (covariantExteriorCandidate connection n form exterior).smooth
    (covariantExteriorCandidate_isHorizontal_unconditional
      IG IB IP smoothBundle connection n form exterior horizontal equivariant)
    (covariantExteriorCandidate_isRightAdEquivariant
      IG IB IP smoothBundle connection n form exterior equivariant)

/-- The descended carrier is exactly the selected-base form of the same principal candidate. -/
@[simp] theorem covariantExteriorDerivativePositive_toForm
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm) :
    (covariantExteriorDerivativePositive IG IB IP smoothBundle connection n form exterior
      horizontal equivariant).toForm =
      selectedBaseForm (IB := IB) (bundle := bundle)
        (covariantExteriorCandidate connection n form exterior).toForm := rfl

/-- Exact quotient representative at the designated local section and tangent lifts. -/
theorem covariantExteriorDerivativePositive_selectedRepresentative
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (b : B) (v : Fin (n + 2) → TangentSpace IB b) :
    (((covariantExteriorDerivativePositive IG IB IP smoothBundle connection n form exterior
      horizontal equivariant).toForm b) v).1 =
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        ((covariantExteriorCandidate connection n form exterior).toForm
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i))) := by
  rw [covariantExteriorDerivativePositive_toForm]
  exact selectedBaseForm_quotient (IB := IB) (IP := IP) (bundle := bundle)
    (covariantExteriorCandidate connection n form exterior).toForm b v

end PrincipalForm

namespace PrincipalConnectionData

/-- The intrinsic smooth adjoint-valued three-form carrier `D_A F` obtained from the exact
same-connection curvature, a same-index curvature structure certificate, and a supplied ordinary
exterior certificate for that curvature. No vanishing statement is made. -/
noncomputable def curvatureCovariantExteriorDerivative
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle 3 :=
  PrincipalForm.covariantExteriorDerivativePositive IG IB IP smoothBundle connection 1
    (connection.curvatureForm exterior) curvatureExterior curvatureStructure.horizontal
      curvatureStructure.right_ad_equivariant

/-- The `D_A F` carrier is exactly the smooth descent of the same curvature candidate. -/
@[simp] theorem curvatureCovariantExteriorDerivative_toForm
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    (curvatureCovariantExteriorDerivative IG IB IP smoothBundle connection exterior curvatureStructure
      curvatureExterior).toForm =
      PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle)
        (PrincipalForm.covariantExteriorCandidate connection 1
          (connection.curvatureForm exterior) curvatureExterior).toForm := rfl

/-- Exact designated quotient representative of the intrinsic `D_A F` three-form. -/
theorem curvatureCovariantExteriorDerivative_selectedRepresentative
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (b : B) (v : Fin 3 → TangentSpace IB b) :
    (((curvatureCovariantExteriorDerivative IG IB IP smoothBundle connection exterior curvatureStructure
      curvatureExterior).toForm b) v).1 =
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        ((PrincipalForm.covariantExteriorCandidate connection 1
          (connection.curvatureForm exterior) curvatureExterior).toForm
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i))) := by
  exact PrincipalForm.covariantExteriorDerivativePositive_selectedRepresentative
    IG IB IP smoothBundle connection 1 (connection.curvatureForm exterior) curvatureExterior
      curvatureStructure.horizontal curvatureStructure.right_ad_equivariant b v

end PrincipalConnectionData

end

end YangMills.Geometry
