/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalNormalizedTrivialization

namespace YangMills.Geometry.PrincipalOrbitAdapted

open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP uα
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

/-- A whole indexed family of prescribed total tangents receives orbit-adapted extensions on one
common open normalized-trivialization source. No intersection of separately chosen domains is used. -/
theorem exists_common_principalAdaptedTotalFields_arbitrary
    {α : Type uα} (p : P) (X : GroupLieAlgebra IG G)
    (v : α → TangentSpace IP p) :
    ∃ (U : Set P) (fields : α → (q : P) → TangentSpace IP q),
      IsOpen U ∧ p ∈ U ∧ (∀ g, torsor.rightAction p g ∈ U) ∧
      (∀ i, fields i p = v i) ∧
      (∀ i, ManifoldTangentField.IsSmoothOn IP U (fields i)) ∧
      (∀ i g, principalRightTranslationDifferential smoothBundle p g (fields i p) =
        fields i (torsor.rightAction p g)) ∧
      (∀ i, VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
        (fields i) U p = 0) := by
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
  let coordinate (i : α) := mfderivWithin IP (IB.prod IG) normalized.toPartialHomeomorph
    normalized.toPartialHomeomorph.source p (v i)
  let fields (i : α) := adaptedTotalField IG IB IP normalized (torsor.projection p)
    (coordinate i).1 (coordinate i).2
  refine ⟨adaptedTotalSource (IB := IB) normalized (torsor.projection p), fields,
    isOpen_adaptedTotalSource IB normalized (torsor.projection p), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hp', by simp [hcoord]⟩
  · intro g
    refine ⟨normalized.rightAction_mem_source hp' g, ?_⟩
    change normalized.toPartialHomeomorph (torsor.rightAction p g) ∈
      (extChartAt IB (torsor.projection p)).source ×ˢ (Set.univ : Set G)
    rw [normalized.rightAction_coordinate p hp' g, hcoord]
    simp
  · intro i
    exact adaptedTotalField_self IG IB IP normalized smoothBundle' hnormalized
      (torsor.projection p) p hp' hcoord (v i)
  · intro i
    exact adaptedTotalField_isSmoothOn IG IB IP normalized smoothBundle' hnormalized
      (torsor.projection p) (coordinate i).1 (coordinate i).2
  · intro i g
    simpa [fields, principalRightTranslationDifferential] using
      adaptedTotalField_rightTranslation IG IB IP normalized smoothBundle' hnormalized
        (torsor.projection p) p hp' hcoord (coordinate i).1 (coordinate i).2 g
  · intro i
    exact mlieBracketWithin_principalFundamental_adaptedTotalField
      IG IB IP normalized smoothBundle' hnormalized (torsor.projection p) p hp' hcoord
        (coordinate i).1 X (coordinate i).2

end

end YangMills.Geometry.PrincipalOrbitAdapted
