/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalOrbitAdaptedTotalField

namespace YangMills.Geometry
open Set Function
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section

variable {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {torsor : PrincipalBundleTorsorData G B P}

/-- Left-translate only the group coordinate. -/
def principalFiberLeftShift (h : G) : (B × G) ≃ₜ (B × G) :=
  (Homeomorph.refl B).prodCongr (Homeomorph.mulLeft h⁻¹)

@[simp] theorem principalFiberLeftShift_apply (h : G) (z : B × G) :
    principalFiberLeftShift (B := B) h z = (z.1, h⁻¹ * z.2) := rfl

@[simp] theorem principalFiberLeftShift_symm_apply (h : G) (z : B × G) :
    (principalFiberLeftShift (B := B) h).symm z = (z.1, h * z.2) := by
  rw [show (principalFiberLeftShift (B := B) h).symm =
    (Homeomorph.refl B).prodCongr (Homeomorph.mulLeft h) by
      simp [principalFiberLeftShift, Homeomorph.mulLeft_symm]]
  rfl

/-- Normalize a principal trivialization by left-translating its group coordinate. -/
def PrincipalBundleLocalTrivialization.normalizeAt
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P) :
    PrincipalBundleLocalTrivialization torsor where
  toPartialHomeomorph := chart.toPartialHomeomorph.transHomeomorph
    (principalFiberLeftShift (B := B) (chart.toPartialHomeomorph p).2)
  baseSet := chart.baseSet
  isOpen_baseSet := chart.isOpen_baseSet
  source_eq := chart.source_eq
  target_eq := by
    ext z
    simp [chart.target_eq, principalFiberLeftShift]
  base_coordinate := by
    intro q hq
    exact chart.base_coordinate q hq
  rightAction_coordinate := by
    intro q hq g
    change principalFiberLeftShift (B := B) (chart.toPartialHomeomorph p).2
        (chart.toPartialHomeomorph (torsor.rightAction q g)) =
      ((principalFiberLeftShift (B := B) (chart.toPartialHomeomorph p).2
        (chart.toPartialHomeomorph q)).1,
       (principalFiberLeftShift (B := B) (chart.toPartialHomeomorph p).2
        (chart.toPartialHomeomorph q)).2 * g)
    rw [chart.rightAction_coordinate q hq g]
    simp only [principalFiberLeftShift_apply]
    rw [mul_assoc]

@[simp] theorem PrincipalBundleLocalTrivialization.normalizeAt_source
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P) :
    (chart.normalizeAt p).toPartialHomeomorph.source = chart.toPartialHomeomorph.source := rfl

@[simp] theorem PrincipalBundleLocalTrivialization.normalizeAt_baseSet
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P) :
    (chart.normalizeAt p).baseSet = chart.baseSet := rfl

@[simp] theorem PrincipalBundleLocalTrivialization.normalizeAt_apply
    (chart : PrincipalBundleLocalTrivialization torsor) (p q : P) :
    (chart.normalizeAt p).toPartialHomeomorph q =
      ((chart.toPartialHomeomorph q).1,
        (chart.toPartialHomeomorph p).2⁻¹ * (chart.toPartialHomeomorph q).2) := rfl

@[simp] theorem PrincipalBundleLocalTrivialization.normalizeAt_self
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P)
    (hp : p ∈ chart.toPartialHomeomorph.source) :
    (chart.normalizeAt p).toPartialHomeomorph p = (torsor.projection p, 1) := by
  rw [chart.normalizeAt_apply, chart.base_coordinate p hp]
  simp

end
end YangMills.Geometry

namespace YangMills.Geometry
open Set Function
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)

omit [ChartedSpace HP P] [IsManifold IP ∞ P] [IsManifold IB ∞ B] in
 theorem principalFiberLeftShift_contMDiff (h : G) :
    ContMDiff (IB.prod IG) (IB.prod IG) ∞ (principalFiberLeftShift (B := B) h) := by
  exact contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)

omit [ChartedSpace HP P] [IsManifold IP ∞ P] [IsManifold IB ∞ B] in
 theorem principalFiberLeftShift_symm_contMDiff (h : G) :
    ContMDiff (IB.prod IG) (IB.prod IG) ∞ (principalFiberLeftShift (B := B) h).symm := by
  rw [show (principalFiberLeftShift (B := B) h).symm =
    (Homeomorph.refl B).prodCongr (Homeomorph.mulLeft h) by
      simp [principalFiberLeftShift, Homeomorph.mulLeft_symm]]
  exact contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)

theorem PrincipalBundleLocalTrivialization.normalizeAt_smoothOn
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (p : P) :
    ContMDiffOn IP (IB.prod IG) ∞ (chart.normalizeAt p).toPartialHomeomorph
      (chart.normalizeAt p).toPartialHomeomorph.source := by
  apply (principalFiberLeftShift_contMDiff IG IB
    (chart.toPartialHomeomorph p).2).comp_contMDiffOn
  exact smoothBundle.trivialization_smooth chart chart_mem

theorem PrincipalBundleLocalTrivialization.normalizeAt_inverse_smoothOn
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (p : P) :
    ContMDiffOn (IB.prod IG) IP ∞ (chart.normalizeAt p).toPartialHomeomorph.symm
      (chart.normalizeAt p).toPartialHomeomorph.target := by
  apply (smoothBundle.inverse_trivialization_smooth chart chart_mem).comp
    (principalFiberLeftShift_symm_contMDiff IG IB
      (chart.toPartialHomeomorph p).2).contMDiffOn
  intro z hz
  exact hz

end
end YangMills.Geometry

namespace YangMills.Geometry
open Set Function
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section

variable {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {torsor : PrincipalBundleTorsorData G B P}

/-- Extend only the designated atlas by one normalized chart. -/
def TopologicalPrincipalBundleData.withNormalizedChart
    (bundle : TopologicalPrincipalBundleData torsor)
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P) :
    TopologicalPrincipalBundleData torsor where
  projection_continuous := bundle.projection_continuous
  rightAction_continuous := bundle.rightAction_continuous
  trivializationAtlas := insert (chart.normalizeAt p) bundle.trivializationAtlas
  trivializationAt := bundle.trivializationAt
  mem_baseSet_trivializationAt := bundle.mem_baseSet_trivializationAt
  trivializationAt_mem_atlas := fun b => Or.inr (bundle.trivializationAt_mem_atlas b)

@[simp] theorem TopologicalPrincipalBundleData.mem_atlas_withNormalizedChart_self
    (bundle : TopologicalPrincipalBundleData torsor)
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P) :
    chart.normalizeAt p ∈ (bundle.withNormalizedChart chart p).trivializationAtlas :=
  Or.inl rfl

end
end YangMills.Geometry

namespace YangMills.Geometry
open Set Function
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)

/-- The smooth structure extends over the inserted normalized chart. -/
def SmoothPrincipalBundleData.withNormalizedChart (p : P) :
    SmoothPrincipalBundleData IB IG IP torsor (bundle.withNormalizedChart chart p) where
  projection_smooth := smoothBundle.projection_smooth
  rightAction_smooth := smoothBundle.rightAction_smooth
  trivialization_smooth := by
    intro c hc
    change c ∈ insert (chart.normalizeAt p) bundle.trivializationAtlas at hc
    rw [Set.mem_insert_iff] at hc
    rcases hc with rfl | hc
    · exact chart.normalizeAt_smoothOn IG IB IP smoothBundle chart_mem p
    · exact smoothBundle.trivialization_smooth c hc
  inverse_trivialization_smooth := by
    intro c hc
    change c ∈ insert (chart.normalizeAt p) bundle.trivializationAtlas at hc
    rw [Set.mem_insert_iff] at hc
    rcases hc with rfl | hc
    · exact chart.normalizeAt_inverse_smoothOn IG IB IP smoothBundle chart_mem p
    · exact smoothBundle.inverse_trivialization_smooth c hc

end
end YangMills.Geometry

namespace YangMills.Geometry.PrincipalOrbitAdapted
open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 2000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- Every total tangent has an orbit-adapted extension, with no coordinate-normalization premise. -/
theorem exists_principalAdaptedTotalField_arbitrary
    (p : P) (v : TangentSpace IP p) (X : GroupLieAlgebra IG G) :
    ∃ (U : Set P) (field : (q : P) → TangentSpace IP q),
      IsOpen U ∧ p ∈ U ∧ field p = v ∧
      ManifoldTangentField.IsSmoothOn IP U field ∧
      (∀ g : G, principalRightTranslationDifferential smoothBundle p g (field p) =
        field (torsor.rightAction p g)) ∧
      VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X) field U p = 0 := by
  let chart := bundle.trivializationAt (torsor.projection p)
  have hp : p ∈ chart.toPartialHomeomorph.source := bundle.mem_source_trivializationAt p
  have hchart : chart ∈ bundle.trivializationAtlas :=
    bundle.trivializationAt_mem_atlas (torsor.projection p)
  let normalized := chart.normalizeAt p
  let bundle' := bundle.withNormalizedChart chart p
  let smoothBundle' : SmoothPrincipalBundleData IB IG IP torsor bundle' :=
    smoothBundle.withNormalizedChart IG IB IP chart hchart p
  have hnormalized : normalized ∈ bundle'.trivializationAtlas := by
    exact TopologicalPrincipalBundleData.mem_atlas_withNormalizedChart_self bundle chart p
  have hp' : p ∈ normalized.toPartialHomeomorph.source := hp
  have hcoord : normalized.toPartialHomeomorph p = (torsor.projection p, (1 : G)) :=
    chart.normalizeAt_self p hp
  obtain ⟨field, hself, hopen, hpU, hsmooth, hright, hbracket⟩ :=
    exists_principalAdaptedTotalField IG IB IP normalized smoothBundle' hnormalized
      (torsor.projection p) p hp' hcoord v X
  refine ⟨adaptedTotalSource (IB := IB) normalized (torsor.projection p), field,
    hopen, hpU, hself, hsmooth, ?_, ?_⟩
  · intro g
    simpa [principalRightTranslationDifferential] using hright g
  · exact hbracket

end
end YangMills.Geometry.PrincipalOrbitAdapted
