/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureGaugePullbackFormula
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph

/-!
# Gauge pullback of exterior data and principal curvature

The reusable diffeomorphism Cartan theorem transports the exact exterior-derivative certificate to
the gauge-pulled connection. The resulting canonical transformed curvature is then proved equal to
the principal total-space pullback of the original curvature.

Mathlib's Lie-bracket pullback theorem requires completeness of the principal total-space model.
This module exposes that condition explicitly and supplies a finite-dimensional specialization.
These are principal pullback equalities, not the local `Ad(g_ϕ⁻¹)` formula, descended curvature
covariance, or gauge invariance of a scalar density, action, or observable.
-/

namespace YangMills.Geometry

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

/-- A smooth gauge automorphism as Mathlib's smooth diffeomorphism carrier. -/
def smoothGaugeDiffeomorph (gauge : SmoothGaugeTransformation smoothBundle) :
    P ≃ₘ^∞⟮IP, IP⟯ P where
  toEquiv := gauge.toGauge.toEquiv
  contMDiff_toFun := gauge.smooth
  contMDiff_invFun := gauge.inverse_smooth

/-- Pull an exact connection-indexed exterior-derivative certificate through a gauge
diffeomorphism. The completeness assumption is precisely the one required by Mathlib's public
Lie-bracket pullback theorem. -/
noncomputable def gaugePullbackConnectionExteriorDerivative [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalConnectionExteriorDerivativeData (gaugePullbackConnection gauge connection) where
  certificate :=
    SmoothManifoldOneFormExteriorDerivativeCertificate.pullbackDiffeomorph
      (smoothGaugeDiffeomorph gauge)
      (groupLieAlgebraModelEquiv IG)
      connection.toSmoothForm exterior.certificate
      (gaugePullbackConnection gauge connection).toSmoothForm
      (by rfl)
      (gaugePullbackExteriorDerivativeForm gauge connection exterior)
      (by rfl)

/-- The derivative carrier of the transformed certificate is exactly the pulled original
certificate derivative. -/
@[simp] theorem gaugePullbackConnectionExteriorDerivative_derivative_toForm [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    (gaugePullbackConnectionExteriorDerivative gauge connection exterior).certificate.derivative.toForm =
      ManifoldDifferentialForm.pullback gauge gauge.smooth
        exterior.certificate.derivative.toForm := by
  rfl

/-- Finite-dimensional total-space models canonically supply the completeness needed for exterior
certificate pullback. -/
noncomputable def gaugePullbackConnectionExteriorDerivative_finiteDimensional
    [FiniteDimensional ℝ EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalConnectionExteriorDerivativeData (gaugePullbackConnection gauge connection) := by
  letI : CompleteSpace EP := FiniteDimensional.complete ℝ EP
  exact gaugePullbackConnectionExteriorDerivative gauge connection exterior

/-- Canonical principal curvature of the gauge-pulled connection equals pullback of the original
principal curvature. This is total-space naturality, not the local adjoint formula. -/
theorem gaugePullbackCurvatureForm_eq_pullback
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    ((gaugePullbackConnection gauge connection).curvatureForm
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm =
      ManifoldDifferentialForm.pullback gauge gauge.smooth
        (connection.curvatureForm exterior).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  change (gaugePulledCurvatureForm gauge connection exterior).toForm = _
  exact gaugePulledCurvatureForm_toForm gauge connection exterior

/-- Evaluated canonical curvature pullback on the exact gauge tangent transports. -/
theorem gaugePullbackCurvatureForm_apply
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (v : Fin 2 → TangentSpace IP p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    ((gaugePullbackConnection gauge connection).curvatureForm
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm p v =
      (connection.curvatureForm exterior).toForm (gauge p)
        (fun i => mfderiv IP IP gauge p (v i)) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [gaugePullbackCurvatureForm_eq_pullback]
  rfl

/-- Finite-dimensional principal and group models provide the canonical curvature pullback theorem
without a caller-supplied completeness instance. -/
theorem gaugePullbackCurvatureForm_eq_pullback_finiteDimensional
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    ((gaugePullbackConnection gauge connection).curvatureForm
      (gaugePullbackConnectionExteriorDerivative_finiteDimensional
        gauge connection exterior)).toForm =
      ManifoldDifferentialForm.pullback gauge gauge.smooth
        (connection.curvatureForm exterior).toForm := by
  letI : CompleteSpace EP := FiniteDimensional.complete ℝ EP
  exact gaugePullbackCurvatureForm_eq_pullback gauge connection exterior

end

end YangMills.Geometry
