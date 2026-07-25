/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothPrincipalBundle
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Local sections and tangent lifts for smooth principal bundles

Every designated principal trivialization supplies a local section by fixing group coordinate `1`.
Its manifold derivative gives a continuous linear tangent lift that is a right inverse to the
bundle-projection differential on the chart base set. This is reusable smooth bundle mathematics
needed before horizontal equivariant principal forms can honestly descend.

No connection, curvature, or descended form is constructed here.
-/

namespace YangMills.Geometry

open Set
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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- Local section associated to a designated principal chart by fixing group coordinate `1`. The
underlying partial-homeomorphism inverse is totalized, while all laws are asserted on `baseSet`. -/
def principalBundleLocalSection
    (chart : PrincipalBundleLocalTrivialization torsor) : B → P :=
  fun b => chart.toPartialHomeomorph.symm (b, (1 : G))

omit [IsTopologicalGroup G] in
/-- The fixed-coordinate pair lies in the chart target over every point of its base set. -/
theorem principalBundleLocalSection_pair_mem_target
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    (b, (1 : G)) ∈ chart.toPartialHomeomorph.target := by
  rw [chart.target_eq]
  exact ⟨hb, Set.mem_univ _⟩

omit [IsTopologicalGroup G] in
/-- The local section projects to the input base point on the chart domain. -/
theorem principalBundleLocalSection_projection
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    torsor.projection (principalBundleLocalSection chart b) = b := by
  have targetMem := principalBundleLocalSection_pair_mem_target chart hb
  have sourceMem := chart.toPartialHomeomorph.map_target targetMem
  calc
    torsor.projection (principalBundleLocalSection chart b) =
        (chart.toPartialHomeomorph (chart.toPartialHomeomorph.symm (b, (1 : G)))).1 :=
      (chart.base_coordinate _ sourceMem).symm
    _ = b := congrArg Prod.fst (chart.toPartialHomeomorph.right_inv targetMem)

/-- The designated local section is smooth on its chart base set. -/
theorem principalBundleLocalSection_contMDiffOn
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn IB IP ∞ (principalBundleLocalSection chart) chart.baseSet := by
  have inputSmooth : ContMDiff IB (IB.prod IG) ∞ (fun b : B => (b, (1 : G))) :=
    contMDiff_id.prodMk contMDiff_const
  have inputMaps : Set.MapsTo (fun b : B => (b, (1 : G))) chart.baseSet
      chart.toPartialHomeomorph.target := by
    intro b hb
    exact principalBundleLocalSection_pair_mem_target chart hb
  change ContMDiffOn IB IP ∞
    (fun b : B => chart.toPartialHomeomorph.symm (b, (1 : G))) chart.baseSet
  exact (smoothBundle.inverse_trivialization_smooth chart chart_mem).comp
    inputSmooth.contMDiffOn inputMaps

/-- The local section is smooth at every point of its chart base set. -/
theorem principalBundleLocalSection_contMDiffAt
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) :
    ContMDiffAt IB IP ∞ (principalBundleLocalSection chart) b :=
  (principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem).contMDiffAt
    (chart.isOpen_baseSet.mem_nhds hb)

/-- Tangent lift supplied by the derivative of a designated local section. -/
def principalBundleLocalTangentLift
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    TangentSpace IB b →L[ℝ]
      TangentSpace IP (principalBundleLocalSection chart b) :=
  mfderiv IB IP (principalBundleLocalSection chart) b

/-- The projection differential composed with the local tangent lift is the identity. -/
theorem principalBundleProjectionDifferential_comp_localTangentLift
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) :
    (mfderiv IP IB torsor.projection (principalBundleLocalSection chart b)).comp
        (principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b) =
      ContinuousLinearMap.id ℝ (TangentSpace IB b) := by
  have sectionSmoothAt :=
    principalBundleLocalSection_contMDiffAt smoothBundle chart chart_mem hb
  have sectionMDiffAt := sectionSmoothAt.mdifferentiableAt (by simp)
  have projectionMDiffAt :=
    (smoothBundle.projection_smooth
      (principalBundleLocalSection chart b)).mdifferentiableAt (by simp)
  have chain := mfderiv_comp b projectionMDiffAt sectionMDiffAt
  have localIdentity :
      (torsor.projection ∘ principalBundleLocalSection chart) =ᶠ[nhds b] id := by
    filter_upwards [chart.isOpen_baseSet.mem_nhds hb] with x hx
    exact principalBundleLocalSection_projection chart hx
  have identityDerivative := localIdentity.mfderiv_eq (I := IB) (I' := IB)
  rw [mfderiv_id] at identityDerivative
  change (mfderiv IP IB torsor.projection (principalBundleLocalSection chart b)).comp
      (mfderiv IB IP (principalBundleLocalSection chart) b) = _
  rw [← chain]
  exact identityDerivative

/-- Pointwise, the local tangent lift is a right inverse to the actual projection differential. -/
theorem principalBundleLocalTangentLift_rightInverse
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) :
    Function.RightInverse
      (principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b)
      (mfderiv IP IB torsor.projection (principalBundleLocalSection chart b)) :=
  ContinuousLinearMap.rightInverse_of_comp
    (principalBundleProjectionDifferential_comp_localTangentLift
      smoothBundle chart chart_mem hb)

end

end YangMills.Geometry
