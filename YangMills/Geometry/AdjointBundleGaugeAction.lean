/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureGaugeStructure
import YangMills.Geometry.PrincipalCurvatureSmoothDescent

/-!
# Gauge action on the actual adjoint bundle quotient

A smooth gauge automorphism induces the set-level map `[p,X] ↦ [ϕ(p),X]` on the actual adjoint
orbit quotient. Representative independence, base preservation, identity, composition, and inverse
laws are derived, then restricted to the exact dependent fibers.

With this covariant convention, curvature of the pulled connection transforms by the **inverse**
induced fiber action. The theorem is proved both for the pointwise descended carrier and evaluations
of the exact smooth descended package. This is covariance, not equality with the original curvature.
Continuity, linearity, and smooth vector-bundle-automorphism packaging of the induced map remain
separate.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

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

namespace SmoothGaugeTransformation

/-- The action induced by a gauge transformation on the adjoint orbit quotient. -/
def inducedAdjointBundleAction
    (gauge : SmoothGaugeTransformation smoothBundle) :
    AdjointBundle (I := IG) torsor → AdjointBundle (I := IG) torsor :=
  Quotient.lift
    (fun z : P × GroupLieAlgebra IG G => AdjointBundle.mk torsor (gauge z.1) z.2)
    (by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      change AdjointBundle.mk torsor (gauge x.1) x.2 =
        AdjointBundle.mk torsor
          (gauge (torsor.rightAction x.1 g))
          (YangMills.Mathematics.lieGroupAdjoint IG g⁻¹ x.2)
      rw [gauge.rightAction_equivariant]
      exact (AdjointBundle.mk_rightAction torsor (gauge x.1) x.2 g).symm)

@[simp]
theorem inducedAdjointBundleAction_mk
    (gauge : SmoothGaugeTransformation smoothBundle)
    (p : P) (X : GroupLieAlgebra IG G) :
    gauge.inducedAdjointBundleAction (AdjointBundle.mk torsor p X) =
      AdjointBundle.mk torsor (gauge p) X :=
  rfl

/-- The induced quotient action preserves the adjoint-bundle projection. -/
theorem inducedAdjointBundleAction_projection
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    AdjointBundle.projection torsor (gauge.inducedAdjointBundleAction z) =
      AdjointBundle.projection torsor z := by
  refine Quotient.inductionOn z ?_
  rintro ⟨p, X⟩
  exact gauge.preserves_projection p

/-- The induced action restricted to one dependent adjoint fiber. -/
def inducedAdjointFiberAction
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B) :
    AdjointBundle.Fiber (I := IG) (torsor := torsor) b →
      AdjointBundle.Fiber (I := IG) (torsor := torsor) b :=
  fun z => ⟨gauge.inducedAdjointBundleAction z.1,
    gauge.inducedAdjointBundleAction_projection z.1 |>.trans z.2⟩

@[simp]
theorem inducedAdjointFiberAction_val
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    (gauge.inducedAdjointFiberAction b z).1 =
      gauge.inducedAdjointBundleAction z.1 :=
  rfl

/-- The identity gauge induces the identity quotient action. -/
@[simp]
theorem inducedAdjointBundleAction_one
    (z : AdjointBundle (I := IG) torsor) :
    (1 : SmoothGaugeTransformation smoothBundle).inducedAdjointBundleAction z = z := by
  refine Quotient.inductionOn z ?_
  rintro ⟨p, X⟩
  rfl

/-- Gauge composition induces composition in the same order. -/
theorem inducedAdjointBundleAction_mul
    (first second : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    (first * second).inducedAdjointBundleAction z =
      first.inducedAdjointBundleAction (second.inducedAdjointBundleAction z) := by
  refine Quotient.inductionOn z ?_
  rintro ⟨p, X⟩
  rfl

/-- The inverse gauge induces a left inverse on the quotient. -/
@[simp]
theorem inducedAdjointBundleAction_inv_apply
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    gauge⁻¹.inducedAdjointBundleAction (gauge.inducedAdjointBundleAction z) = z := by
  rw [← inducedAdjointBundleAction_mul]
  simp

/-- The inverse gauge induces a right inverse on the quotient. -/
@[simp]
theorem inducedAdjointBundleAction_apply_inv
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    gauge.inducedAdjointBundleAction (gauge⁻¹.inducedAdjointBundleAction z) = z := by
  rw [← inducedAdjointBundleAction_mul]
  simp

/-- Identity on each dependent fiber. -/
@[simp]
theorem inducedAdjointFiberAction_one
    (b : B) (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    (1 : SmoothGaugeTransformation smoothBundle).inducedAdjointFiberAction b z = z := by
  apply Subtype.ext
  exact inducedAdjointBundleAction_one z.1

/-- Composition on each dependent fiber. -/
theorem inducedAdjointFiberAction_mul
    (first second : SmoothGaugeTransformation smoothBundle)
    (b : B) (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    (first * second).inducedAdjointFiberAction b z =
      first.inducedAdjointFiberAction b (second.inducedAdjointFiberAction b z) := by
  apply Subtype.ext
  exact inducedAdjointBundleAction_mul first second z.1

/-- The inverse gauge induces a left inverse on each dependent fiber. -/
@[simp]
theorem inducedAdjointFiberAction_inv_apply
    (gauge : SmoothGaugeTransformation smoothBundle)
    (b : B) (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    gauge⁻¹.inducedAdjointFiberAction b (gauge.inducedAdjointFiberAction b z) = z := by
  apply Subtype.ext
  exact inducedAdjointBundleAction_inv_apply gauge z.1

/-- The inverse gauge induces a right inverse on each dependent fiber. -/
@[simp]
theorem inducedAdjointFiberAction_apply_inv
    (gauge : SmoothGaugeTransformation smoothBundle)
    (b : B) (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    gauge.inducedAdjointFiberAction b (gauge⁻¹.inducedAdjointFiberAction b z) = z := by
  apply Subtype.ext
  exact inducedAdjointBundleAction_apply_inv gauge z.1

end SmoothGaugeTransformation

open SmoothGaugeTransformation

/-- The pointwise descended curvature of a gauge-pulled connection is the inverse induced gauge
    action on the original descended curvature. -/
theorem gaugePullbackPointwiseBaseCurvature_eq_inverseInducedAction
    [FiniteDimensional ℝ EG] [CompleteSpace EP]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) (v : Fin 2 → TangentSpace IB b) :
    ((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v =
      gauge⁻¹.inducedAdjointFiberAction b
        ((connection.pointwiseBaseCurvature exterior b) v) := by
  apply Subtype.ext
  let p := principalBundleLocalSection (bundle.trivializationAt b) b
  let X := (connection.curvatureForm exterior).toForm p
    (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
      (bundle.trivializationAt b) b (v i))
  let g := gauge.associatedGaugeFunction p
  have hpull :
      (((gaugePullbackConnection gauge connection).pointwiseBaseCurvature
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior) b) v).1 =
        AdjointBundle.mk torsor (torsor.rightAction p g⁻¹) X := by
    simpa [p, X, g] using
      gaugePullbackPointwiseBaseCurvature_quotient_eq_inverseShift
        gauge connection exterior certificate b v
  have horiginal :
      ((connection.pointwiseBaseCurvature exterior b) v).1 =
        AdjointBundle.mk torsor p X := by
    simpa [p, X] using connection.pointwiseBaseCurvature_quotient exterior b v
  rw [inducedAdjointFiberAction_val, hpull, horiginal]
  let left := AdjointBundle.mk torsor (torsor.rightAction p g⁻¹) X
  let right := gauge⁻¹.inducedAdjointBundleAction (AdjointBundle.mk torsor p X)
  have h : gauge.inducedAdjointBundleAction left =
      gauge.inducedAdjointBundleAction right := by
    calc
      gauge.inducedAdjointBundleAction left = AdjointBundle.mk torsor p X := by
        simp only [left, inducedAdjointBundleAction_mk]
        rw [gauge.rightAction_equivariant,
          gauge.eq_rightAction_associatedGaugeFunction, torsor.right_mul]
        simp [g, torsor.right_one]
      _ = gauge.inducedAdjointBundleAction right := by
        exact (inducedAdjointBundleAction_apply_inv gauge
          (AdjointBundle.mk torsor p X)).symm
  calc
    left = gauge⁻¹.inducedAdjointBundleAction
        (gauge.inducedAdjointBundleAction left) :=
      (inducedAdjointBundleAction_inv_apply gauge left).symm
    _ = gauge⁻¹.inducedAdjointBundleAction
        (gauge.inducedAdjointBundleAction right) := congrArg _ h
    _ = right := inducedAdjointBundleAction_inv_apply gauge right

/-- The same covariance statement for the exact smooth descended curvature packages. -/
theorem gaugePullbackSmoothBaseCurvature_eq_inverseInducedAction
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
        (((connection.smoothBaseCurvature exterior certificate).toForm b) v) := by
  exact gaugePullbackPointwiseBaseCurvature_eq_inverseInducedAction
    gauge connection exterior certificate b v

end

end YangMills.Geometry
