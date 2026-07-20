/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureLocalGaugeAdjoint

/-!
# Hostile probes for the associated gauge function and local adjoint curvature law
-/

namespace YangMills.Geometry.PrincipalCurvatureLocalGaugeAdjoint.Probes

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The selected associated function realizes the exact gauge action with fixed orientation. -/
theorem exact_associated_gauge_action
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) :
    gauge p = torsor.rightAction p (gauge.associatedGaugeFunction p) :=
  gauge.eq_rightAction_associatedGaugeFunction p

/-- No different group element can realize the same action at the same torsor point. -/
theorem exact_associated_gauge_uniqueness
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (g : G)
    (action_eq : gauge p = torsor.rightAction p g) :
    gauge.associatedGaugeFunction p = g :=
  gauge.associatedGaugeFunction_eq_of_rightAction p g action_eq

/-- Right translation changes the associated function by the exact conjugation orientation. -/
theorem exact_associated_gauge_conjugation
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (h : G) :
    gauge.associatedGaugeFunction (torsor.rightAction p h) =
      h⁻¹ * gauge.associatedGaugeFunction p * h :=
  gauge.associatedGaugeFunction_rightAction p h

/-- Reversing or otherwise changing the conjugation law is rejected. -/
theorem malformed_associated_gauge_conjugation_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (h : G)
    (wrong : gauge.associatedGaugeFunction (torsor.rightAction p h) ≠
      h⁻¹ * gauge.associatedGaugeFunction p * h) : False :=
  wrong (gauge.associatedGaugeFunction_rightAction p h)

/-- The exact gauge tangent map preserves the projected base tangent. -/
theorem exact_gauge_projection_derivative
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (v : TangentSpace IP p) :
    mfderiv IP IB torsor.projection (gauge p) (mfderiv IP IP gauge p v) =
      mfderiv IP IB torsor.projection p v :=
  gauge.mfderiv_projection p v

/-- Canonical transformed curvature obeys the exact local `Ad(g_ϕ⁻¹)` law. -/
theorem exact_local_adjoint_curvature
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (p : P) (v : Fin 2 → TangentSpace IP p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    ((gaugePullbackConnection gauge connection).curvatureForm
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
        ((connection.curvatureForm exterior).toForm p v) :=
  gaugePullbackCurvatureForm_apply_associatedGaugeFunction
    gauge connection exterior certificate p v

/-- Finite-dimensional models discharge the local law's completeness premise. -/
theorem exact_finiteDimensional_local_adjoint_curvature
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (p : P) (v : Fin 2 → TangentSpace IP p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    ((gaugePullbackConnection gauge connection).curvatureForm
      (gaugePullbackConnectionExteriorDerivative_finiteDimensional
        gauge connection exterior)).toForm p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
        ((connection.curvatureForm exterior).toForm p v) :=
  gaugePullbackCurvatureForm_apply_associatedGaugeFunction_finiteDimensional
    gauge connection exterior certificate p v

/-- The non-inverted adjoint factor is rejected whenever it differs from the sourced inverse law. -/
theorem wrong_adjoint_inverse_blocked
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (p : P) (v : Fin 2 → TangentSpace IP p)
    (factors_differ :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          ((connection.curvatureForm exterior).toForm p v) ≠
        lieGroupAdjoint IG (gauge.associatedGaugeFunction p)
          ((connection.curvatureForm exterior).toForm p v))
    (wrong :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      ((gaugePullbackConnection gauge connection).curvatureForm
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm p v =
        lieGroupAdjoint IG (gauge.associatedGaugeFunction p)
          ((connection.curvatureForm exterior).toForm p v)) : False := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact factors_differ
    ((gaugePullbackCurvatureForm_apply_associatedGaugeFunction
      gauge connection exterior certificate p v).symm.trans wrong)

end

end YangMills.Geometry.PrincipalCurvatureLocalGaugeAdjoint.Probes
