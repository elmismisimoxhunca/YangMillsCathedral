/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeSmoothVectorBundleAutomorphism

/-!
# Hostile probes for the smooth dependent adjoint-bundle gauge automorphism
-/

namespace YangMills.Geometry.AdjointBundleGaugeSmoothVectorBundleAutomorphism.Probes

open Set
open scoped Manifold ContDiff Bundle Topology
open SmoothGaugeTransformation

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The dependent local fiber coordinate is the exact forward adjoint action. -/
theorem exact_dependent_local_formula
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
    (hz : z ∈ (AdjointBundle.dependentModelBundleTrivialization
      (I := IG) bundle chart).source) :
    let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
    (e (gauge.inducedAdjointDependentTotalSpaceAction z)).2 =
      YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
        (gauge.associatedGaugeFunction (principalBundleLocalSection chart (e z).1)) (e z).2 :=
  inducedAdjointDependentTotalSpaceAction_modelBundleTrivialization_snd gauge chart z hz

/-- The exact dependent action is globally smooth in the named smooth-vector-bundle structure. -/
theorem exact_dependent_global_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := IG) bundle
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    letI : ContMDiffVectorBundle ∞ EG
        (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
      AdjointBundle.dependentContMDiffVectorBundle smoothBundle
    ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      gauge.inducedAdjointDependentTotalSpaceAction :=
  inducedAdjointDependentTotalSpaceAction_contMDiff gauge

/-- Diffeomorphism packaging retains the exact dependent action carrier. -/
theorem exact_dependent_diffeomorphism_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := IG) bundle
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    letI : ContMDiffVectorBundle ∞ EG
        (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
      AdjointBundle.dependentContMDiffVectorBundle smoothBundle
    inducedAdjointDependentTotalSpaceDiffeomorph gauge z =
      gauge.inducedAdjointDependentTotalSpaceAction z := rfl

/-- The inverse diffeomorphism carrier is exactly the inverse-gauge dependent action. -/
theorem exact_dependent_diffeomorphism_inverse_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := IG) bundle
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    letI : ContMDiffVectorBundle ∞ EG
        (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
      AdjointBundle.dependentContMDiffVectorBundle smoothBundle
    (inducedAdjointDependentTotalSpaceDiffeomorph gauge).symm z =
      gauge⁻¹.inducedAdjointDependentTotalSpaceAction z := rfl

/-- The diffeomorphism's fiber component is exactly the established continuous-linear equivalence. -/
theorem exact_continuousLinear_fiber_restriction
    (gauge : SmoothGaugeTransformation smoothBundle)
    (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentFiberBundle (I := IG) bundle
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    letI : ContMDiffVectorBundle ∞ EG
        (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
      AdjointBundle.dependentContMDiffVectorBundle smoothBundle
    (inducedAdjointDependentTotalSpaceDiffeomorph gauge ⟨b, z⟩).2 =
      gauge.inducedAdjointFiberContinuousLinearEquiv b z := rfl

/-- A mismatched diffeomorphism carrier is rejected. -/
theorem mismatched_dependent_diffeomorphism_carrier_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
    (wrong :
      letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      letI : TopologicalSpace
          (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
      letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
        AdjointBundle.dependentFiberBundle (I := IG) bundle
      letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
        AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
      letI : ContMDiffVectorBundle ∞ EG
          (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
        AdjointBundle.dependentContMDiffVectorBundle smoothBundle
      inducedAdjointDependentTotalSpaceDiffeomorph gauge z ≠
        gauge.inducedAdjointDependentTotalSpaceAction z) : False :=
  wrong rfl

/-- A nonsmooth dependent action contradicts the exact local-coordinate globalization. -/
theorem nonsmooth_dependent_action_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong :
      letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      letI : TopologicalSpace
          (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
      letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
        AdjointBundle.dependentFiberBundle (I := IG) bundle
      letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
        AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
      letI : ContMDiffVectorBundle ∞ EG
          (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
        AdjointBundle.dependentContMDiffVectorBundle smoothBundle
      ¬ ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
        gauge.inducedAdjointDependentTotalSpaceAction) : False :=
  wrong (inducedAdjointDependentTotalSpaceAction_contMDiff gauge)

/-- A malformed dependent local formula is rejected on the exact chart source. -/
theorem malformed_dependent_formula_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
    (hz : z ∈ (AdjointBundle.dependentModelBundleTrivialization
      (I := IG) bundle chart).source)
    (wrong :
      let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
      (e (gauge.inducedAdjointDependentTotalSpaceAction z)).2 ≠
        YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
          (gauge.associatedGaugeFunction (principalBundleLocalSection chart (e z).1)) (e z).2) :
    False :=
  wrong (inducedAdjointDependentTotalSpaceAction_modelBundleTrivialization_snd gauge chart z hz)

end

end YangMills.Geometry.AdjointBundleGaugeSmoothVectorBundleAutomorphism.Probes
