/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionGaugeExteriorDerivative
import YangMills.Geometry.PrincipalTwoFormRepresentativeIndependence

/-!
# Associated gauge function and local adjoint curvature law

The torsor property canonically assigns to every gauge automorphism the unique group element
`g_ϕ(p)` satisfying `ϕ(p) = p · g_ϕ(p)`. Its right-action conjugation law is derived. Differentiated
projection preservation and curvature horizontality compare the gauge tangent map with fixed right
translation; right-adjoint equivariance then proves Freed's evaluated local law
`F_{ϕ* A}(p) = Ad(g_ϕ(p)⁻¹) F_A(p)` for the exact canonical pulled curvature.

The associated function is noncomputably selected from unique torsor data. This module does not yet
prove its smoothness or the affine connection formula involving its Maurer--Cartan derivative. It
also does not imply descended, scalar-density, action, or observable gauge invariance.
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

/-- The canonical group element taking `p` to its image under a gauge automorphism. -/
noncomputable def SmoothGaugeTransformation.associatedGaugeFunction
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) : G :=
  Classical.choose (torsor.fiber_unique p (gauge p) (gauge.preserves_projection p).symm)

/-- The canonical associated gauge function represents the gauge automorphism pointwise. -/
theorem SmoothGaugeTransformation.eq_rightAction_associatedGaugeFunction
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) :
    gauge p = torsor.rightAction p (gauge.associatedGaugeFunction p) :=
  (Classical.choose_spec
    (torsor.fiber_unique p (gauge p) (gauge.preserves_projection p).symm)).1.symm

/-- The associated gauge function is the unique group element realizing the pointwise action. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_eq_of_rightAction
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (g : G)
    (action_eq : gauge p = torsor.rightAction p g) :
    gauge.associatedGaugeFunction p = g := by
  symm
  exact (Classical.choose_spec
    (torsor.fiber_unique p (gauge p) (gauge.preserves_projection p).symm)).2 g action_eq.symm

/-- The canonical associated gauge function transforms by conjugation under the right action. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_rightAction
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (h : G) :
    gauge.associatedGaugeFunction (torsor.rightAction p h) =
      h⁻¹ * gauge.associatedGaugeFunction p * h := by
  symm
  apply (Classical.choose_spec
    (torsor.fiber_unique (torsor.rightAction p h)
      (gauge (torsor.rightAction p h))
      (gauge.preserves_projection (torsor.rightAction p h)).symm)).2
  rw [torsor.right_mul, gauge.rightAction_equivariant,
    gauge.eq_rightAction_associatedGaugeFunction, torsor.right_mul]
  simp [mul_assoc]

/-- The gauge tangent map projects to the original base tangent vector. -/
theorem SmoothGaugeTransformation.mfderiv_projection
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (v : TangentSpace IP p) :
    mfderiv IP IB torsor.projection (gauge p) (mfderiv IP IP gauge p v) =
      mfderiv IP IB torsor.projection p v := by
  have hfun : torsor.projection ∘ (gauge : P → P) = torsor.projection := by
    funext q
    exact gauge.preserves_projection q
  have hderiv := mfderiv_congr (I := IP) (I' := IB) (x := p) hfun
  rw [mfderiv_comp p
      (smoothBundle.projection_smooth.mdifferentiableAt (by simp))
      (gauge.smooth.mdifferentiableAt (by simp))] at hderiv
  exact congrArg (fun L => L v) hderiv

/-- Evaluated local adjoint law for the canonical curvature of the gauge-pulled connection. -/
theorem gaugePullbackCurvatureForm_apply_associatedGaugeFunction
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
        ((connection.curvatureForm exterior).toForm p v) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [gaugePullbackCurvatureForm_apply]
  let g := gauge.associatedGaugeFunction p
  have hpoint : gauge p = torsor.rightAction p g :=
    gauge.eq_rightAction_associatedGaugeFunction p
  have hequivariant := certificate.right_ad_equivariant g p v
  rw [← hpoint] at hequivariant
  have hrightProjection (i : Fin 2) :=
    principalBundleProjectionDifferential_rightTranslation_apply smoothBundle p g (v i)
  rw [← hpoint] at hrightProjection
  calc
    (connection.curvatureForm exterior).toForm (gauge p)
        (fun i => mfderiv IP IP gauge p (v i)) =
      (connection.curvatureForm exterior).toForm (gauge p)
        (fun i => principalRightTranslationDifferential smoothBundle p g (v i)) := by
          apply certificate.horizontal.eq_of_projection_eq smoothBundle
          intro i
          rw [gauge.mfderiv_projection]
          exact (hrightProjection i).symm
    _ = lieGroupAdjoint IG g⁻¹
        ((connection.curvatureForm exterior).toForm p v) :=
      hequivariant

/-- Finite-dimensional group and total-space models derive every completeness premise for the
local adjoint curvature law. -/
theorem gaugePullbackCurvatureForm_apply_associatedGaugeFunction_finiteDimensional
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
        ((connection.curvatureForm exterior).toForm p v) := by
  letI : CompleteSpace EP := FiniteDimensional.complete ℝ EP
  exact gaugePullbackCurvatureForm_apply_associatedGaugeFunction
    gauge connection exterior certificate p v

end

end YangMills.Geometry
