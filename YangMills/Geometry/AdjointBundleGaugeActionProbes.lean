/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeAction

/-!
# Hostile probes for the induced adjoint-bundle gauge action
-/

namespace YangMills.Geometry.AdjointBundleGaugeAction.Probes

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

open SmoothGaugeTransformation

/-- The quotient action uses the exact representative formula `[p,X] ↦ [ϕ(p),X]`. -/
theorem exact_quotient_representative
    (gauge : SmoothGaugeTransformation smoothBundle)
    (p : P) (X : GroupLieAlgebra IG G) :
    gauge.inducedAdjointBundleAction (AdjointBundle.mk torsor p X) =
      AdjointBundle.mk torsor (gauge p) X :=
  gauge.inducedAdjointBundleAction_mk p X

/-- The induced quotient action remains in the exact same base fiber. -/
theorem exact_projection_preservation
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    AdjointBundle.projection torsor (gauge.inducedAdjointBundleAction z) =
      AdjointBundle.projection torsor z :=
  gauge.inducedAdjointBundleAction_projection z

/-- Gauge multiplication acts in the same covariant order on quotient values. -/
theorem exact_composition
    (first second : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    (first * second).inducedAdjointBundleAction z =
      first.inducedAdjointBundleAction (second.inducedAdjointBundleAction z) :=
  inducedAdjointBundleAction_mul first second z

/-- The induced inverse is an exact inverse on every dependent fiber. -/
theorem exact_fiber_inverse
    (gauge : SmoothGaugeTransformation smoothBundle)
    (b : B) (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    gauge⁻¹.inducedAdjointFiberAction b (gauge.inducedAdjointFiberAction b z) = z :=
  inducedAdjointFiberAction_inv_apply gauge b z

/-- Pointwise descended curvature transforms by the inverse induced fiber action. -/
theorem exact_pointwise_inverse_covariance
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
    ((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v =
      gauge⁻¹.inducedAdjointFiberAction b
        ((connection.pointwiseBaseCurvature exterior b) v) :=
  gaugePullbackPointwiseBaseCurvature_eq_inverseInducedAction
    gauge connection exterior certificate b v

/-- Evaluations of the exact smooth descended package obey the same inverse covariance. -/
theorem exact_smooth_descended_evaluation_covariance
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
    (((gaugePullbackConnection gauge connection).smoothBaseCurvature
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (gaugePullbackCurvatureStructureCertificate
          gauge connection exterior certificate)).toForm b) v =
      gauge⁻¹.inducedAdjointFiberAction b
        (((connection.smoothBaseCurvature exterior certificate).toForm b) v) :=
  gaugePullbackSmoothBaseCurvature_eq_inverseInducedAction
    gauge connection exterior certificate b v

/-- Reversing composition order is rejected whenever the two quotient actions differ. -/
theorem reversed_composition_blocked_when_distinct
    (first second : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor)
    (orders_differ :
      first.inducedAdjointBundleAction (second.inducedAdjointBundleAction z) ≠
        second.inducedAdjointBundleAction (first.inducedAdjointBundleAction z))
    (wrong : (first * second).inducedAdjointBundleAction z =
      second.inducedAdjointBundleAction (first.inducedAdjointBundleAction z)) : False :=
  orders_differ ((inducedAdjointBundleAction_mul first second z).symm.trans wrong)

/-- Using the forward induced action for pulled curvature is rejected whenever forward and inverse
fiber actions differ on the exact original value. -/
theorem wrong_forward_curvature_action_blocked
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b)
    (orientations_differ :
      gauge⁻¹.inducedAdjointFiberAction b
          ((connection.pointwiseBaseCurvature exterior b) v) ≠
        gauge.inducedAdjointFiberAction b
          ((connection.pointwiseBaseCurvature exterior b) v))
    (wrong :
      ((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
          (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v =
        gauge.inducedAdjointFiberAction b
          ((connection.pointwiseBaseCurvature exterior b) v)) : False :=
  orientations_differ
    ((gaugePullbackPointwiseBaseCurvature_eq_inverseInducedAction
      gauge connection exterior certificate b v).symm.trans wrong)

end

end YangMills.Geometry.AdjointBundleGaugeAction.Probes
