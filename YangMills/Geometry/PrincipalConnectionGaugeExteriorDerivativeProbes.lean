/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionGaugeExteriorDerivative

/-!
# Hostile probes for gauge-pulled exterior data and canonical curvature
-/

namespace YangMills.Geometry.PrincipalConnectionGaugeExteriorDerivative.Probes

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

/-- The transformed certificate derivative is exactly the original derivative pullback. -/
theorem exact_transformed_derivative [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    (gaugePullbackConnectionExteriorDerivative gauge connection exterior).certificate.derivative.toForm =
      ManifoldDifferentialForm.pullback gauge gauge.smooth
        exterior.certificate.derivative.toForm :=
  gaugePullbackConnectionExteriorDerivative_derivative_toForm gauge connection exterior

/-- The canonical same-index transformed curvature is the exact principal pullback. -/
theorem exact_canonical_curvature_pullback
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
        (connection.curvatureForm exterior).toForm :=
  gaugePullbackCurvatureForm_eq_pullback gauge connection exterior

/-- Canonical curvature evaluation transports both ordered tangent slots by the exact gauge map. -/
theorem exact_canonical_curvature_evaluation
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
        (fun i => mfderiv IP IP gauge p (v i)) :=
  gaugePullbackCurvatureForm_apply gauge connection exterior p v

/-- Finite-dimensional models discharge the completeness premise without caller data. -/
theorem exact_finiteDimensional_canonical_curvature_pullback
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
        (connection.curvatureForm exterior).toForm :=
  gaugePullbackCurvatureForm_eq_pullback_finiteDimensional gauge connection exterior

/-- A disconnected transformed derivative carrier is rejected. -/
theorem unrelated_transformed_derivative_blocked [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (wrong :
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior).certificate.derivative.toForm ≠
        ManifoldDifferentialForm.pullback gauge gauge.smooth
          exterior.certificate.derivative.toForm) : False :=
  wrong (gaugePullbackConnectionExteriorDerivative_derivative_toForm
    gauge connection exterior)

/-- A non-pullback canonical transformed curvature contradicts Cartan-certificate naturality. -/
theorem malformed_canonical_curvature_blocked
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (wrong :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      ((gaugePullbackConnection gauge connection).curvatureForm
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm ≠
        ManifoldDifferentialForm.pullback gauge gauge.smooth
          (connection.curvatureForm exterior).toForm) : False :=
  wrong (gaugePullbackCurvatureForm_eq_pullback gauge connection exterior)

end

end YangMills.Geometry.PrincipalConnectionGaugeExteriorDerivative.Probes
