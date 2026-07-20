/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureLocalGaugeAdjoint
import YangMills.Geometry.PrincipalCurvaturePointwiseDescent

/-!
# Gauge transport of curvature structure and pointwise descent

Canonical gauge pullback preserves the exact curvature's horizontality and right-adjoint
equivariance, so the transformed connection receives a derived structure certificate. The
pointwise descended adjoint-bundle curvature is then described by two equivalent quotient
representatives: the selected section with an `Ad(g_ϕ⁻¹)` coefficient, or an inverse-shifted
principal representative with the original coefficient.

This is adjoint-bundle covariance, not equality with the original adjoint-valued curvature. Scalar
contraction, action, and observable invariance remain separate.
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

/-- Gauge pullback preserves the horizontal/right-adjoint-equivariant curvature structure. -/
noncomputable def gaugePullbackCurvatureStructureCertificate
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    PrincipalCurvatureStructureCertificate smoothBundle
      (gaugePullbackConnection gauge connection)
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior) where
  horizontal := by
    intro p v hvertical
    rw [gaugePullbackCurvatureForm_apply]
    apply certificate.horizontal
    obtain ⟨i, hi⟩ := hvertical
    refine ⟨i, ?_⟩
    rw [gauge.mfderiv_projection, hi]
    rfl
  right_ad_equivariant := by
    intro g p v
    rw [gaugePullbackCurvatureForm_apply, gaugePullbackCurvatureForm_apply]
    let sourceLifts : Fin 2 → TangentSpace IP (gauge p) :=
      fun i => mfderiv IP IP gauge p (v i)
    have hequivariant :=
      certificate.right_ad_equivariant g (gauge p) sourceLifts
    rw [← gauge.rightAction_equivariant p g] at hequivariant
    calc
      (connection.curvatureForm exterior).toForm
          (gauge (torsor.rightAction p g))
          (fun i => mfderiv IP IP gauge (torsor.rightAction p g)
            (principalRightTranslationDifferential smoothBundle p g (v i))) =
        (connection.curvatureForm exterior).toForm
          (gauge (torsor.rightAction p g))
          (fun i => principalRightTranslationDifferential smoothBundle (gauge p) g
            (sourceLifts i)) := by
        congr 1
        funext i
        exact gauge_mfderiv_principalRightTranslationDifferential gauge p g (v i)
      _ = lieGroupAdjoint IG g⁻¹
          ((connection.curvatureForm exterior).toForm (gauge p) sourceLifts) :=
        hequivariant

/-- Finite-dimensional total-space models provide the completeness required above. -/
noncomputable def gaugePullbackCurvatureStructureCertificate_finiteDimensional
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    PrincipalCurvatureStructureCertificate smoothBundle
      (gaugePullbackConnection gauge connection)
      (gaugePullbackConnectionExteriorDerivative_finiteDimensional
        gauge connection exterior) := by
  letI : CompleteSpace EP := FiniteDimensional.complete ℝ EP
  exact gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate

/-- Exact representative formula for the pointwise descended gauge-pulled curvature. -/
theorem gaugePullbackPointwiseBaseCurvature_quotient
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
    (((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v).1 =
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        (lieGroupAdjoint IG
          (gauge.associatedGaugeFunction
            (principalBundleLocalSection (bundle.trivializationAt b) b))⁻¹
          ((connection.curvatureForm exterior).toForm
            (principalBundleLocalSection (bundle.trivializationAt b) b)
            (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
              (bundle.trivializationAt b) b (v i)))) := by
  rw [PrincipalConnectionData.pointwiseBaseCurvature_quotient]
  rw [gaugePullbackCurvatureForm_apply_associatedGaugeFunction
    gauge connection exterior certificate]

/-- The same descended value can be represented by shifting the selected principal representative
by the inverse associated gauge-function value while retaining the original curvature coefficient. -/
theorem gaugePullbackPointwiseBaseCurvature_quotient_eq_inverseShift
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
    (((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v).1 =
      AdjointBundle.mk torsor
        (torsor.rightAction
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (gauge.associatedGaugeFunction
            (principalBundleLocalSection (bundle.trivializationAt b) b))⁻¹)
        ((connection.curvatureForm exterior).toForm
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i))) := by
  rw [gaugePullbackPointwiseBaseCurvature_quotient
    gauge connection exterior certificate]
  let p := principalBundleLocalSection (bundle.trivializationAt b) b
  let g := gauge.associatedGaugeFunction p
  let X := (connection.curvatureForm exterior).toForm p
    (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
      (bundle.trivializationAt b) b (v i))
  have h := AdjointBundle.mk_rightAction torsor
    (torsor.rightAction p g⁻¹) X g
  rw [torsor.right_mul, inv_mul_cancel, torsor.right_one] at h
  simpa [p, g, X] using h

end

end YangMills.Geometry
