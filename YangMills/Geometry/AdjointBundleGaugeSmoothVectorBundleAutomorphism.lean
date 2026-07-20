/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeDiffeomorph
import YangMills.Geometry.AdjointBundleSmoothVectorBundle
import YangMills.Geometry.AdjointBundleSmoothAtlas
import YangMills.Geometry.SmoothGaugeAssociatedFunction
import Mathlib.Geometry.Manifold.Diffeomorph

namespace YangMills.Geometry

/-!
# Smooth dependent adjoint-bundle gauge automorphism

The covariant action `[p,X] ↦ [ϕ(p),X]` is smooth on the dependent adjoint-bundle total space
carrying the exact named smooth vector-bundle structure. In local bundle coordinates its fiber
component is `Ad(g_ϕ(s(b)))X`. Applying the same argument to the inverse gauge transformation
packages the already established total-space homeomorphism as a `C∞` diffeomorphism. Its fixed
fiber restrictions remain the exact continuous real-linear equivalences established earlier.

This is bundle-automorphism packaging only. It does not assert that curvature, scalar densities,
actions, or observables are invariant.
-/

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

set_option pp.universes false in
set_option pp.all false in
theorem inducedAdjointBundleAction_modelBundleTrivialization_of_mem_source
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : AdjointBundle (I := IG) torsor)
    (hz : z ∈ (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).source) :
    let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
    let w := e z
    e (gauge.inducedAdjointBundleAction z) =
      (w.1, YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
        (gauge.associatedGaugeFunction (principalBundleLocalSection chart w.1)) w.2) := by
  let e := AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
  let w := e z
  have hw : w ∈ e.target := e.toOpenPartialHomeomorph.map_source hz
  have hb : w.1 ∈ chart.baseSet := e.mem_target.mp hw
  let p := principalBundleLocalSection chart w.1
  let intrinsic := YangMills.Mathematics.groupLieAlgebraModelEquiv (G := G) IG
  let X : GroupLieAlgebra IG G := intrinsic.symm w.2
  have hzrep : z = AdjointBundle.mk torsor p X := by
    rw [← e.toOpenPartialHomeomorph.left_inv hz]
    change e.toOpenPartialHomeomorph.symm w = AdjointBundle.mk torsor p X
    rw [AdjointBundle.modelBundleTrivialization_symm_apply]
    rfl
  let k := gauge.associatedGaugeFunction p
  have hmk := AdjointBundle.mk_rightAction torsor p
    (YangMills.Mathematics.lieGroupAdjoint IG k X) k
  rw [YangMills.Mathematics.lieGroupAdjoint_inv_apply] at hmk
  have haction : gauge.inducedAdjointBundleAction z =
      AdjointBundle.mk torsor p (YangMills.Mathematics.lieGroupAdjoint IG k X) := by
    rw [hzrep, inducedAdjointBundleAction_mk,
      gauge.eq_rightAction_associatedGaugeFunction]
    exact hmk
  rw [haction]
  change AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
      (AdjointBundle.mk torsor p (YangMills.Mathematics.lieGroupAdjoint IG k X)) = _
  rw [AdjointBundle.modelBundleTrivialization_apply]
  have hpTarget := principalBundleLocalSection_pair_mem_target chart hb
  have hpSource : p ∈ chart.toPartialHomeomorph.source :=
    chart.toPartialHomeomorph.map_target hpTarget
  have hpCoordinate : chart.toPartialHomeomorph p = (w.1, (1 : G)) :=
    chart.toPartialHomeomorph.right_inv hpTarget
  rw [AdjointBundle.localCoordinate_mk chart p _ hpSource, hpCoordinate,
    YangMills.Mathematics.lieGroupAdjoint_one]
  simp only [ContinuousLinearMap.id_apply]
  apply Prod.ext
  · change torsor.projection p = w.1
    exact principalBundleLocalSection_projection chart hb
  · change intrinsic (YangMills.Mathematics.lieGroupAdjoint IG k X) =
      YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG) k w.2
    change YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG) k (intrinsic X) =
      YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG) k w.2
    congr 1


set_option pp.universes false in
set_option pp.all false in
theorem inducedAdjointDependentTotalSpaceAction_modelBundleTrivialization_snd
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
    (hz : z ∈ (AdjointBundle.dependentModelBundleTrivialization
      (I := IG) bundle chart).source) :
    let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
    (e (gauge.inducedAdjointDependentTotalSpaceAction z)).2 =
      YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
        (gauge.associatedGaugeFunction (principalBundleLocalSection chart (e z).1)) (e z).2 := by
  let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
  have hq : AdjointBundle.totalSpaceToQuotient (I := IG) (torsor := torsor) z ∈
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).source := hz
  have h := inducedAdjointBundleAction_modelBundleTrivialization_of_mem_source gauge chart
    (AdjointBundle.totalSpaceToQuotient (I := IG) (torsor := torsor) z) hq
  exact congrArg Prod.snd h

/-- The induced action is smooth on the exact dependent total-space manifold. -/
theorem inducedAdjointDependentTotalSpaceAction_contMDiff
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
      gauge.inducedAdjointDependentTotalSpaceAction := by
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
  intro z
  let chart := bundle.trivializationAt z.proj
  let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
  letI : MemTrivializationAtlas e :=
    ⟨⟨chart, bundle.trivializationAt_mem_atlas z.proj, rfl⟩⟩
  have hz : z ∈ e.source := e.mem_source.mpr (bundle.mem_baseSet_trivializationAt z.proj)
  have hgz : gauge.inducedAdjointDependentTotalSpaceAction z ∈ e.source := by
    apply e.mem_source.mpr
    exact bundle.mem_baseSet_trivializationAt z.proj
  apply (e.contMDiffAt_iff hgz).mpr
  constructor
  · simpa only [inducedAdjointDependentTotalSpaceAction_proj] using
      (Bundle.contMDiff_proj (n := ∞) (𝕜 := ℝ)
        (AdjointBundle.Fiber (I := IG) (torsor := torsor))).contMDiffAt
  · have heSmooth : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞ e z :=
      (e.contMDiffOn z hz).contMDiffAt (e.open_source.mem_nhds hz)
    have hb : (e z).1 ∈ chart.baseSet := by
      rw [e.coe_fst hz]
      exact bundle.mem_baseSet_trivializationAt z.proj
    have hlocal : ContMDiffAt IB IG ∞
        (fun b => gauge.associatedGaugeFunction (principalBundleLocalSection chart b)) (e z).1 :=
      (gauge.associatedGaugeFunction_localSection_contMDiffOn chart
        (bundle.trivializationAt_mem_atlas z.proj) (e z).1 hb).contMDiffAt
          (chart.isOpen_baseSet.mem_nhds hb)
    have hgauge : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) IG ∞
        (fun y => gauge.associatedGaugeFunction
          (principalBundleLocalSection chart (e y).1)) z :=
      hlocal.comp z heSmooth.fst
    have hop : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) 𝓘(ℝ, EG →L[ℝ] EG) ∞
        (fun y => YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
          (gauge.associatedGaugeFunction (principalBundleLocalSection chart (e y).1))) z :=
      (YangMills.Mathematics.lieGroupAdjointCoordinates_contMDiff
        (I := IG) (G := G)).contMDiffAt.comp z hgauge
    have hcand : ContMDiffAt (IB.prod 𝓘(ℝ, EG)) 𝓘(ℝ, EG) ∞
        (fun y => YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
          (gauge.associatedGaugeFunction (principalBundleLocalSection chart (e y).1))
          (e y).2) z :=
      hop.clm_apply heSmooth.snd
    apply hcand.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hz] with y hy
    exact inducedAdjointDependentTotalSpaceAction_modelBundleTrivialization_snd gauge chart y hy

/-- The induced action packaged as a dependent-total-space `C∞` diffeomorphism. -/
def inducedAdjointDependentTotalSpaceDiffeomorph
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
    Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))
      ≃ₘ^∞⟮IB.prod 𝓘(ℝ, EG), IB.prod 𝓘(ℝ, EG)⟯
    Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) := by
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
  exact
    { toEquiv := gauge.inducedAdjointDependentTotalSpaceHomeomorph.toEquiv
      contMDiff_toFun := inducedAdjointDependentTotalSpaceAction_contMDiff gauge
      contMDiff_invFun := inducedAdjointDependentTotalSpaceAction_contMDiff gauge⁻¹ }


end
end YangMills.Geometry
