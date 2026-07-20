/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeContinuousLinear
import YangMills.Geometry.AdjointBundleDependentFiberTopology

/-!
# Topological gauge automorphism of the adjoint bundle

Continuity of `[p,X] ↦ [ϕ(p),X]` descends through the defining quotient map, giving a quotient
homeomorphism with inverse induced by `ϕ⁻¹`. Conjugating by the exact dependent-total-space/
quotient homeomorphism produces a base-preserving homeomorphism of the named dependent total-space
topology. Its fiber restrictions are the previously derived continuous-linear equivalences.

No smooth-manifold or smooth vector-bundle automorphism is claimed here.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff Bundle Topology

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

namespace SmoothGaugeTransformation

/-- The quotient-induced gauge action is continuous for the defining quotient topology. -/
theorem inducedAdjointBundleAction_continuous
    (gauge : SmoothGaugeTransformation smoothBundle) :
    Continuous gauge.inducedAdjointBundleAction := by
  rw [(AdjointBundle.mk_isQuotientMap (I := IG) (torsor := torsor)).continuous_iff]
  exact (AdjointBundle.mk_continuous (I := IG) (torsor := torsor)).comp
    (gauge.smooth.continuous.prodMap continuous_id)

/-- The quotient action and inverse-gauge action form an exact homeomorphism. -/
def inducedAdjointBundleHomeomorph
    (gauge : SmoothGaugeTransformation smoothBundle) :
    AdjointBundle (I := IG) torsor ≃ₜ AdjointBundle (I := IG) torsor where
  toFun := gauge.inducedAdjointBundleAction
  invFun := gauge⁻¹.inducedAdjointBundleAction
  left_inv := gauge.inducedAdjointBundleAction_inv_apply
  right_inv := gauge.inducedAdjointBundleAction_apply_inv
  continuous_toFun := gauge.inducedAdjointBundleAction_continuous
  continuous_invFun := gauge⁻¹.inducedAdjointBundleAction_continuous

/-- Direct base-preserving action on the exact dependent total-space carrier. -/
def inducedAdjointDependentTotalSpaceAction
    (gauge : SmoothGaugeTransformation smoothBundle) :
    Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) →
      Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
  fun z => ⟨z.proj, gauge.inducedAdjointFiberAction z.proj z.snd⟩

/-- The dependent action preserves the displayed base definitionally. -/
@[simp] theorem inducedAdjointDependentTotalSpaceAction_proj
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    (gauge.inducedAdjointDependentTotalSpaceAction z).proj = z.proj := rfl

/-- On each fixed fiber, the dependent action is exactly the previously bundled continuous-linear
equivalence. -/
theorem inducedAdjointDependentTotalSpaceAction_fiber
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (gauge.inducedAdjointDependentTotalSpaceAction ⟨b, z⟩).snd =
      gauge.inducedAdjointFiberContinuousLinearEquiv b z := by
  exact (gauge.inducedAdjointFiberContinuousLinearEquiv_apply b z).symm

/-- The direct dependent carrier is exactly conjugation of the quotient action through the
established carrier homeomorphism. -/
theorem inducedAdjointDependentTotalSpaceAction_eq_conjugate
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    gauge.inducedAdjointDependentTotalSpaceAction z =
      (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
        (I := IG) (torsor := torsor)).symm
        (gauge.inducedAdjointBundleHomeomorph
          (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
            (I := IG) (torsor := torsor) z)) := by
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  apply (AdjointBundle.totalSpaceEquivQuotient
    (I := IG) (torsor := torsor)).injective
  rfl

/-- The direct dependent action is a homeomorphism for the named quotient-induced topology. -/
def inducedAdjointDependentTotalSpaceHomeomorph
    (gauge : SmoothGaugeTransformation smoothBundle) :
    @Homeomorph
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
      (AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor))
      (AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)) := by
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  exact
    { toFun := gauge.inducedAdjointDependentTotalSpaceAction
      invFun := gauge⁻¹.inducedAdjointDependentTotalSpaceAction
      left_inv := by
        intro z
        apply (AdjointBundle.totalSpaceEquivQuotient
          (I := IG) (torsor := torsor)).injective
        exact gauge.inducedAdjointBundleAction_inv_apply z.snd.1
      right_inv := by
        intro z
        apply (AdjointBundle.totalSpaceEquivQuotient
          (I := IG) (torsor := torsor)).injective
        exact gauge.inducedAdjointBundleAction_apply_inv z.snd.1
      continuous_toFun := by
        let conjugate :=
          (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
            (I := IG) (torsor := torsor)).trans
            (gauge.inducedAdjointBundleHomeomorph.trans
              (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
                (I := IG) (torsor := torsor)).symm)
        exact conjugate.continuous.congr fun z =>
          (gauge.inducedAdjointDependentTotalSpaceAction_eq_conjugate z).symm
      continuous_invFun := by
        let conjugate :=
          (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
            (I := IG) (torsor := torsor)).trans
            (gauge⁻¹.inducedAdjointBundleHomeomorph.trans
              (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
                (I := IG) (torsor := torsor)).symm)
        exact conjugate.continuous.congr fun z =>
          (gauge⁻¹.inducedAdjointDependentTotalSpaceAction_eq_conjugate z).symm }

@[simp] theorem inducedAdjointDependentTotalSpaceHomeomorph_apply
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    gauge.inducedAdjointDependentTotalSpaceHomeomorph z =
      gauge.inducedAdjointDependentTotalSpaceAction z :=
  rfl

@[simp] theorem inducedAdjointDependentTotalSpaceHomeomorph_symm_apply
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    gauge.inducedAdjointDependentTotalSpaceHomeomorph.symm z =
      gauge⁻¹.inducedAdjointDependentTotalSpaceAction z :=
  rfl

end SmoothGaugeTransformation
end
end YangMills.Geometry
