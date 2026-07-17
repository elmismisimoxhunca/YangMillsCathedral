/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.TopologicalPrincipalBundle
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth principal bundles

This module adds manifold structures and smooth compatibility to the topological principal-bundle
atlas. It does not define connections or curvature.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

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

/-- Smooth compatibility data for a fixed topological principal bundle.

Every designated local homeomorphism and its inverse are smooth on their declared domains. This
makes smooth overlap compatibility derivable rather than storing unrelated transition functions. -/
structure SmoothPrincipalBundleData
    (IB : ModelWithCorners ℝ EB HB)
    (IG : ModelWithCorners ℝ EG HG)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    (torsor : PrincipalBundleTorsorData G B P)
    (bundle : TopologicalPrincipalBundleData torsor) : Prop where
  /-- The bundle projection is smooth. -/
  projection_smooth : ContMDiff IP IB ∞ torsor.projection
  /-- The uncurried right action is smooth. -/
  rightAction_smooth :
    ContMDiff (IP.prod IG) IP ∞ fun pg : P × G => torsor.rightAction pg.1 pg.2
  /-- Every chart in the designated atlas is smooth on its source. -/
  trivialization_smooth : ∀ chart ∈ bundle.trivializationAtlas,
    ContMDiffOn IP (IB.prod IG) ∞ chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source
  /-- Every inverse chart is smooth on its target. -/
  inverse_trivialization_smooth : ∀ chart ∈ bundle.trivializationAtlas,
    ContMDiffOn (IB.prod IG) IP ∞ chart.toPartialHomeomorph.symm
      chart.toPartialHomeomorph.target

/-- Coordinate-domain on which the transition from `first` to `second` is meaningful. -/
def principalBundleOverlapDomain {torsor : PrincipalBundleTorsorData G B P}
    (first second : PrincipalBundleLocalTrivialization torsor) : Set (B × G) :=
  first.toPartialHomeomorph.target ∩
    first.toPartialHomeomorph.symm ⁻¹' second.toPartialHomeomorph.source

/-- Change of local product coordinates from `first` to `second`. -/
def principalBundleTransition {torsor : PrincipalBundleTorsorData G B P}
    (first second : PrincipalBundleLocalTrivialization torsor) : B × G → B × G :=
  fun z => second.toPartialHomeomorph (first.toPartialHomeomorph.symm z)

omit [IsTopologicalGroup G] in
/-- The natural domain of a principal-bundle overlap transition is open. -/
theorem isOpen_principalBundleOverlapDomain
    {torsor : PrincipalBundleTorsorData G B P}
    (first second : PrincipalBundleLocalTrivialization torsor) :
    IsOpen (principalBundleOverlapDomain first second) :=
  first.toPartialHomeomorph.isOpen_inter_preimage_symm
    second.toPartialHomeomorph.open_source

omit [IsTopologicalGroup G] in
/-- A transition carries its overlap domain into the overlap domain in the reverse direction. -/
theorem principalBundleTransition_mem_reverseOverlap
    {torsor : PrincipalBundleTorsorData G B P}
    (first second : PrincipalBundleLocalTrivialization torsor) (z : B × G)
    (memOverlap : z ∈ principalBundleOverlapDomain first second) :
    principalBundleTransition first second z ∈
      principalBundleOverlapDomain second first := by
  have inverse_mem_first := first.toPartialHomeomorph.map_target memOverlap.1
  have inverse_mem_second : first.toPartialHomeomorph.symm z ∈
      second.toPartialHomeomorph.source := memOverlap.2
  constructor
  · exact second.toPartialHomeomorph.map_source inverse_mem_second
  · change second.toPartialHomeomorph.symm
      (second.toPartialHomeomorph (first.toPartialHomeomorph.symm z)) ∈
        first.toPartialHomeomorph.source
    rw [second.toPartialHomeomorph.left_inv inverse_mem_second]
    exact inverse_mem_first

omit [IsTopologicalGroup G] in
/-- Reversing an overlap coordinate transition recovers the original coordinate. -/
theorem principalBundleTransition_reverse
    {torsor : PrincipalBundleTorsorData G B P}
    (first second : PrincipalBundleLocalTrivialization torsor) (z : B × G)
    (memOverlap : z ∈ principalBundleOverlapDomain first second) :
    principalBundleTransition second first (principalBundleTransition first second z) = z := by
  have inverse_mem_second : first.toPartialHomeomorph.symm z ∈
      second.toPartialHomeomorph.source := memOverlap.2
  change first.toPartialHomeomorph
    (second.toPartialHomeomorph.symm
      (second.toPartialHomeomorph (first.toPartialHomeomorph.symm z))) = z
  rw [second.toPartialHomeomorph.left_inv inverse_mem_second,
    first.toPartialHomeomorph.right_inv memOverlap.1]

omit [IsTopologicalGroup G] in
/-- A principal-bundle coordinate transition preserves the base coordinate on its overlap domain. -/
theorem principalBundleTransition_fst {torsor : PrincipalBundleTorsorData G B P}
    (first second : PrincipalBundleLocalTrivialization torsor) (z : B × G)
    (memOverlap : z ∈ principalBundleOverlapDomain first second) :
    (principalBundleTransition first second z).1 = z.1 := by
  have inverse_mem_first := first.toPartialHomeomorph.map_target memOverlap.1
  have inverse_mem_second : first.toPartialHomeomorph.symm z ∈
      second.toPartialHomeomorph.source := memOverlap.2
  calc
    (principalBundleTransition first second z).1 =
        torsor.projection (first.toPartialHomeomorph.symm z) :=
      second.base_coordinate _ inverse_mem_second
    _ = (first.toPartialHomeomorph (first.toPartialHomeomorph.symm z)).1 :=
      (first.base_coordinate _ inverse_mem_first).symm
    _ = z.1 := by rw [first.toPartialHomeomorph.right_inv memOverlap.1]

namespace SmoothPrincipalBundleData

/-- Overlap transitions between designated atlas charts are smooth on their natural domains. -/
theorem transition_smoothOn
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (first second : PrincipalBundleLocalTrivialization torsor)
    (first_mem : first ∈ bundle.trivializationAtlas)
    (second_mem : second ∈ bundle.trivializationAtlas) :
    ContMDiffOn (IB.prod IG) (IB.prod IG) ∞
      (principalBundleTransition first second)
      (principalBundleOverlapDomain first second) := by
  have inverse_smooth := smoothBundle.inverse_trivialization_smooth first first_mem
  have second_smooth := smoothBundle.trivialization_smooth second second_mem
  apply second_smooth.comp (inverse_smooth.mono Set.inter_subset_left)
  intro z memOverlap
  exact memOverlap.2

/-- The global product principal bundle has its expected smooth structure. -/
def trivial
    (IB : ModelWithCorners ℝ EB HB)
    (IG : ModelWithCorners ℝ EG HG)
    {G : Type uG} {B : Type uB}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [IsTopologicalGroup G]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B] :
    SmoothPrincipalBundleData IB IG (IB.prod IG)
      (PrincipalBundleTorsorData.trivial G B)
      (TopologicalPrincipalBundleData.trivial G B) := by
  refine {
    projection_smooth := contMDiff_fst
    rightAction_smooth := ?_
    trivialization_smooth := ?_
    inverse_trivialization_smooth := ?_
  }
  · exact (contMDiff_fst.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp contMDiff_fst).mul contMDiff_snd)
  · intro chart memAtlas
    simp only [TopologicalPrincipalBundleData.trivial, Set.mem_singleton_iff] at memAtlas
    subst chart
    exact contMDiff_id.contMDiffOn
  · intro chart memAtlas
    simp only [TopologicalPrincipalBundleData.trivial, Set.mem_singleton_iff] at memAtlas
    subst chart
    exact contMDiff_id.contMDiffOn

end SmoothPrincipalBundleData

end YangMills.Geometry
