/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureGaugeStructure

/-!
# Hostile probes for gauge-transported curvature structure and descent
-/

namespace YangMills.Geometry.PrincipalCurvatureGaugeStructure.Probes

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
    [FiniteDimensional ℝ EG]

/-- Gauge pullback derives horizontality for the exact transformed canonical curvature. -/
theorem exact_transformed_horizontality [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    PrincipalTwoForm.IsHorizontal smoothBundle
      ((gaugePullbackConnection gauge connection).curvatureForm
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm :=
  (gaugePullbackCurvatureStructureCertificate
    gauge connection exterior certificate).horizontal

/-- Gauge pullback derives right-adjoint equivariance with the same group convention. -/
theorem exact_transformed_rightAdjointEquivariance [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    PrincipalTwoForm.IsRightAdEquivariant smoothBundle
      ((gaugePullbackConnection gauge connection).curvatureForm
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm :=
  (gaugePullbackCurvatureStructureCertificate
    gauge connection exterior certificate).right_ad_equivariant

/-- Finite-dimensional total-space models derive the exact transformed certificate. -/
theorem exact_finiteDimensional_structure
    [FiniteDimensional ℝ EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior) :
    Nonempty (PrincipalCurvatureStructureCertificate smoothBundle
      (gaugePullbackConnection gauge connection)
      (gaugePullbackConnectionExteriorDerivative_finiteDimensional
        gauge connection exterior)) :=
  ⟨gaugePullbackCurvatureStructureCertificate_finiteDimensional
    gauge connection exterior certificate⟩

/-- The pointwise descended transformed curvature has the exact inverse-adjoint coefficient. -/
theorem exact_pointwise_descended_adjoint_coefficient [CompleteSpace EP]
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
              (bundle.trivializationAt b) b (v i)))) :=
  gaugePullbackPointwiseBaseCurvature_quotient
    gauge connection exterior certificate b v

/-- The same quotient value has the exact inverse-shifted principal representative. -/
theorem exact_pointwise_descended_inverseShift [CompleteSpace EP]
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
            (bundle.trivializationAt b) b (v i))) :=
  gaugePullbackPointwiseBaseCurvature_quotient_eq_inverseShift
    gauge connection exterior certificate b v

/-- A nonzero transformed value with a vertical slot contradicts the derived certificate. -/
theorem nonhorizontal_transformed_curvature_blocked [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (p : P) (v : Fin 2 → TangentSpace IP p)
    (vertical : ∃ i, mfderiv IP IB torsor.projection p (v i) = 0)
    (nonzero : ((gaugePullbackConnection gauge connection).curvatureForm
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior)).toForm p v ≠ 0) :
    False :=
  nonzero ((gaugePullbackCurvatureStructureCertificate
    gauge connection exterior certificate).horizontal p v vertical)

/-- A malformed descended coefficient is rejected against the exact quotient formula. -/
theorem malformed_descended_coefficient_blocked [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b)
    (wrong :
      (((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v).1 ≠
        AdjointBundle.mk torsor
          (principalBundleLocalSection (bundle.trivializationAt b) b)
          (lieGroupAdjoint IG
            (gauge.associatedGaugeFunction
              (principalBundleLocalSection (bundle.trivializationAt b) b))⁻¹
            ((connection.curvatureForm exterior).toForm
              (principalBundleLocalSection (bundle.trivializationAt b) b)
              (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
                (bundle.trivializationAt b) b (v i))))) : False :=
  wrong (gaugePullbackPointwiseBaseCurvature_quotient
    gauge connection exterior certificate b v)

end

end YangMills.Geometry.PrincipalCurvatureGaugeStructure.Probes
