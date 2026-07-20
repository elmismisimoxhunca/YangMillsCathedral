/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeContinuousLinear

/-!
# Hostile probes for continuous-linear gauge actions on adjoint fibers
-/

namespace YangMills.Geometry.AdjointBundleGaugeContinuousLinear.Probes

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

/-- In selected coordinates the forward covariant action is exactly `Ad(g_ϕ)`, not its inverse. -/
theorem exact_selected_coordinate_action
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    let chart := bundle.trivializationAt b
    let hb := bundle.mem_baseSet_trivializationAt b
    let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv
      (IG := IG) (bundle := bundle) chart hb
    let p := principalBundleLocalSection chart b
    coordinate (gauge.inducedAdjointFiberAction b z) =
      lieGroupAdjointCoordinatesEquiv (I := IG)
        (gauge.associatedGaugeFunction p) (coordinate z) :=
  inducedAdjointFiberAction_coordinate gauge b z

/-- Using `Ad(g_ϕ⁻¹)` for the forward selected-coordinate action is rejected whenever it differs
from the exact covariant orientation. -/
theorem wrong_forward_selected_coordinate_inverse_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (orientations_differ :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      let chart := bundle.trivializationAt b
      let hb := bundle.mem_baseSet_trivializationAt b
      let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv
        (IG := IG) (bundle := bundle) chart hb
      let p := principalBundleLocalSection chart b
      lieGroupAdjointCoordinatesEquiv (I := IG)
          (gauge.associatedGaugeFunction p) (coordinate z) ≠
        lieGroupAdjointCoordinatesEquiv (I := IG)
          (gauge.associatedGaugeFunction p)⁻¹ (coordinate z))
    (wrong :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      let chart := bundle.trivializationAt b
      let hb := bundle.mem_baseSet_trivializationAt b
      let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv
        (IG := IG) (bundle := bundle) chart hb
      let p := principalBundleLocalSection chart b
      coordinate (gauge.inducedAdjointFiberAction b z) =
        lieGroupAdjointCoordinatesEquiv (I := IG)
          (gauge.associatedGaugeFunction p)⁻¹ (coordinate z)) : False :=
  orientations_differ
    ((inducedAdjointFiberAction_coordinate gauge b z).symm.trans wrong)

/-- The continuous-linear equivalence retains exactly the existing quotient-induced carrier. -/
theorem exact_continuousLinear_carrier
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    gauge.inducedAdjointFiberContinuousLinearEquiv b z =
      gauge.inducedAdjointFiberAction b z :=
  gauge.inducedAdjointFiberContinuousLinearEquiv_apply b z

/-- The bundled inverse is exactly the inverse gauge action. -/
theorem exact_continuousLinear_inverse
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (gauge.inducedAdjointFiberContinuousLinearEquiv b).symm z =
      gauge⁻¹.inducedAdjointFiberAction b z :=
  gauge.inducedAdjointFiberContinuousLinearEquiv_symm_apply b z

/-- Identity acts as the exact reflexive continuous-linear equivalence. -/
theorem exact_continuousLinear_identity (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (1 : SmoothGaugeTransformation smoothBundle).inducedAdjointFiberContinuousLinearEquiv b =
      ContinuousLinearEquiv.refl ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
  inducedAdjointFiberContinuousLinearEquiv_one b

/-- Gauge multiplication is bundled composition in the exact covariant order. -/
theorem exact_continuousLinear_composition
    (first second : SmoothGaugeTransformation smoothBundle) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (first * second).inducedAdjointFiberContinuousLinearEquiv b =
      (second.inducedAdjointFiberContinuousLinearEquiv b).trans
        (first.inducedAdjointFiberContinuousLinearEquiv b) :=
  inducedAdjointFiberContinuousLinearEquiv_mul first second b

/-- A disconnected continuous-linear carrier is rejected. -/
theorem mismatched_continuousLinear_carrier_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (wrong :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      gauge.inducedAdjointFiberContinuousLinearEquiv b z ≠
        gauge.inducedAdjointFiberAction b z) : False :=
  wrong (gauge.inducedAdjointFiberContinuousLinearEquiv_apply b z)

/-- The inverse operator cannot be replaced by the forward action when they differ. -/
theorem wrong_continuousLinear_inverse_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (orientations_differ :
      gauge⁻¹.inducedAdjointFiberAction b z ≠ gauge.inducedAdjointFiberAction b z)
    (wrong :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      (gauge.inducedAdjointFiberContinuousLinearEquiv b).symm z =
        gauge.inducedAdjointFiberAction b z) : False :=
  orientations_differ
    ((gauge.inducedAdjointFiberContinuousLinearEquiv_symm_apply b z).symm.trans wrong)

end

end YangMills.Geometry.AdjointBundleGaugeContinuousLinear.Probes
