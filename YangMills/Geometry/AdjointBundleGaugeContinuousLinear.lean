/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeAction
import YangMills.Geometry.AdjointBundleDependentFiberTopologicalModule

/-!
# Continuous-linear gauge action on adjoint fibers

In the selected quotient-derived coordinate, the covariant induced gauge action is exactly
`Ad(g_ϕ(s(b)))`, with no inverse. Conjugating this model continuous-linear equivalence by the exact
fiber coordinate packages the pre-existing set-level action as a continuous real-linear
automorphism of every dependent adjoint fiber. Its inverse carrier is exactly the inverse gauge
action.

This is fiberwise packaging only. Joint dependent-total-space continuity and a smooth vector-bundle
automorphism remain separate goals.
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

open SmoothGaugeTransformation

set_option pp.universes false in
set_option pp.all false in
 theorem inducedAdjointFiberAction_coordinate
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
    let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) (bundle := bundle) chart hb
    let p := principalBundleLocalSection chart b
    coordinate (gauge.inducedAdjointFiberAction b z) =
      YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG)
        (gauge.associatedGaugeFunction p) (coordinate z) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let chart := bundle.trivializationAt b
  let hb := bundle.mem_baseSet_trivializationAt b
  let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) (bundle := bundle) chart hb
  let p := principalBundleLocalSection chart b
  let g := gauge.associatedGaugeFunction p
  let intrinsic := YangMills.Mathematics.groupLieAlgebraModelEquiv (G := G) IG
  let X : GroupLieAlgebra IG G := intrinsic.symm (coordinate z)
  let representative : AdjointBundle.Fiber (I := IG) (torsor := torsor) b :=
    ⟨AdjointBundle.mk torsor p X, by
      rw [AdjointBundle.projection_mk, principalBundleLocalSection_projection chart hb]⟩
  have hrepresentative : representative = z := by
    apply coordinate.injective
    rw [AdjointBundle.fiberModelContinuousLinearEquiv_apply]
    rw [AdjointBundle.fiberModelEquiv_localSection_mk (IG := IG) (bundle := bundle) chart hb X]
    exact intrinsic.apply_symm_apply (coordinate z)
  let transformed : AdjointBundle.Fiber (I := IG) (torsor := torsor) b :=
    ⟨AdjointBundle.mk torsor p (YangMills.Mathematics.lieGroupAdjoint IG g X), by
      rw [AdjointBundle.projection_mk, principalBundleLocalSection_projection chart hb]⟩
  have haction : gauge.inducedAdjointFiberAction b representative = transformed := by
    apply Subtype.ext
    rw [inducedAdjointFiberAction_val, inducedAdjointBundleAction_mk,
      gauge.eq_rightAction_associatedGaugeFunction]
    have hm := AdjointBundle.mk_rightAction torsor p
      (YangMills.Mathematics.lieGroupAdjoint IG g X) g
    rw [YangMills.Mathematics.lieGroupAdjoint_inv_apply] at hm
    exact hm
  rw [← hrepresentative, haction]
  change coordinate transformed =
    YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG) g
      (coordinate representative)
  rw [AdjointBundle.fiberModelContinuousLinearEquiv_apply]
  rw [AdjointBundle.fiberModelEquiv_localSection_mk (IG := IG) (bundle := bundle) chart hb]
  rw [AdjointBundle.fiberModelContinuousLinearEquiv_apply]
  rw [AdjointBundle.fiberModelEquiv_localSection_mk (IG := IG) (bundle := bundle) chart hb]
  rfl

namespace SmoothGaugeTransformation

/-- The exact induced action bundled as a continuous real-linear equivalence of one dependent
adjoint fiber. -/
def inducedAdjointFiberContinuousLinearEquiv
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    AdjointBundle.Fiber (I := IG) (torsor := torsor) b ≃L[ℝ]
      AdjointBundle.Fiber (I := IG) (torsor := torsor) b := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  let chart := bundle.trivializationAt b
  let hb := bundle.mem_baseSet_trivializationAt b
  let coordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
  let p := principalBundleLocalSection chart b
  let modelAction := YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG)
    (gauge.associatedGaugeFunction p)
  let expected := coordinate.trans (modelAction.trans coordinate.symm)
  let inverseCoordinate := AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb
  let inverseP := principalBundleLocalSection chart b
  let inverseModelAction := YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG)
    (gauge⁻¹.associatedGaugeFunction inverseP)
  let expectedInverse := inverseCoordinate.trans (inverseModelAction.trans inverseCoordinate.symm)
  have hforward (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
      gauge.inducedAdjointFiberAction b z = expected z := by
    apply coordinate.injective
    change coordinate (gauge.inducedAdjointFiberAction b z) = coordinate (expected z)
    rw [inducedAdjointFiberAction_coordinate gauge b z]
    change modelAction (coordinate z) = coordinate (expected z)
    simp only [expected, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hinverse (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
      gauge⁻¹.inducedAdjointFiberAction b z = expectedInverse z := by
    apply inverseCoordinate.injective
    change inverseCoordinate (gauge⁻¹.inducedAdjointFiberAction b z) =
      inverseCoordinate (expectedInverse z)
    rw [inducedAdjointFiberAction_coordinate gauge⁻¹ b z]
    change inverseModelAction (inverseCoordinate z) = inverseCoordinate (expectedInverse z)
    simp only [expectedInverse, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  exact
    { toFun := gauge.inducedAdjointFiberAction b
      invFun := gauge⁻¹.inducedAdjointFiberAction b
      map_add' := by
        intro x y
        rw [hforward, hforward, hforward]
        exact map_add expected x y
      map_smul' := by
        intro c x
        rw [hforward, hforward]
        exact map_smul expected c x
      left_inv := gauge.inducedAdjointFiberAction_inv_apply b
      right_inv := gauge.inducedAdjointFiberAction_apply_inv b
      continuous_toFun := expected.continuous.congr (fun z => (hforward z).symm)
      continuous_invFun := expectedInverse.continuous.congr (fun z => (hinverse z).symm) }

@[simp]
theorem inducedAdjointFiberContinuousLinearEquiv_apply
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
  rfl

@[simp]
theorem inducedAdjointFiberContinuousLinearEquiv_symm_apply
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
  rfl

/-- Identity is exact at the bundled continuous-linear-equivalence level. -/
@[simp] theorem inducedAdjointFiberContinuousLinearEquiv_one (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (1 : SmoothGaugeTransformation smoothBundle).inducedAdjointFiberContinuousLinearEquiv b =
      ContinuousLinearEquiv.refl ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  ext z
  rw [inducedAdjointFiberContinuousLinearEquiv_apply]
  simp

/-- Gauge multiplication is exact composition in the covariant action order. -/
theorem inducedAdjointFiberContinuousLinearEquiv_mul
    (first second : SmoothGaugeTransformation smoothBundle) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (first * second).inducedAdjointFiberContinuousLinearEquiv b =
      (second.inducedAdjointFiberContinuousLinearEquiv b).trans
        (first.inducedAdjointFiberContinuousLinearEquiv b) := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  ext z
  rw [inducedAdjointFiberContinuousLinearEquiv_apply]
  change (first * second).inducedAdjointFiberAction b z =
    first.inducedAdjointFiberContinuousLinearEquiv b
      (second.inducedAdjointFiberContinuousLinearEquiv b z)
  rw [inducedAdjointFiberContinuousLinearEquiv_apply,
    inducedAdjointFiberContinuousLinearEquiv_apply]
  exact inducedAdjointFiberAction_mul first second b z

end SmoothGaugeTransformation

end

end YangMills.Geometry
