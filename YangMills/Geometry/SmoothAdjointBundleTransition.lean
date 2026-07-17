/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleTransition

/-!
# Smoothness of adjoint-bundle overlap transitions

The exact overlap transition previously derived from quotient coordinates is now proved smooth on
its natural open domain. The proof composes the designated smooth principal transition with the
generally derived smooth adjoint action; it does not introduce a separate smoothness witness.

This supplies the analytic input for a future fiberwise-linear manifold atlas. It does not install a
charted-space, manifold, `FiberBundle`, or `VectorBundle` instance.
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
    (first second : PrincipalBundleLocalTrivialization torsor)
    (first_mem : first ∈ bundle.trivializationAtlas)
    (second_mem : second ∈ bundle.trivializationAtlas)

include smoothBundle first_mem second_mem in
set_option backward.isDefEq.respectTransparency false in
/-- The group component `k₁₂(b)` of the principal transition, evaluated at group coordinate `1`,
is smooth on the associated overlap domain. -/
theorem adjointBundleTransitionGroup_contMDiffOn :
    ContMDiffOn (IB.prod 𝓘(ℝ, EG)) IG ∞
      (fun z : B × EG =>
        (principalBundleTransition first second (z.1, (1 : G))).2)
      (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG)) := by
  have unitInput : ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod IG) ∞
      (fun z : B × EG => (z.1, (1 : G))) :=
    contMDiff_fst.prodMk contMDiff_const
  have unitMaps : Set.MapsTo
      (fun z : B × EG => (z.1, (1 : G)))
      (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG))
      (principalBundleOverlapDomain first second) := by
    intro z hz
    exact hz
  have transitionSmooth := SmoothPrincipalBundleData.transition_smoothOn
    smoothBundle first second first_mem second_mem
  have composed := transitionSmooth.comp unitInput.contMDiffOn unitMaps
  simpa [Function.comp_def] using contMDiff_snd.comp_contMDiffOn composed

/-- Model-coordinate formula for the associated transition. This is the exact formula reached
from the quotient transition after applying the canonical tangent-model identification. -/
def adjointBundleTransitionCoordinates (z : B × EG) : B × EG :=
  (z.1, YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
    (principalBundleTransition first second (z.1, (1 : G))).2 z.2)

/-- The fiber operator of the associated transition as a continuous linear equivalence. -/
def adjointBundleTransitionEquiv (b : B) : EG ≃L[ℝ] EG :=
  YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv (I := IG)
    (principalBundleTransition first second (b, (1 : G))).2

include smoothBundle first_mem second_mem in
/-- The forward operator-valued transition family is smooth on the intersection of the two base
sets. -/
theorem adjointBundleTransitionEquiv_contMDiffOn :
    ContMDiffOn IB 𝓘(ℝ, EG →L[ℝ] EG) ∞
      (fun b : B => (adjointBundleTransitionEquiv (IG := IG) first second b).toContinuousLinearMap)
      (first.baseSet ∩ second.baseSet) := by
  let baseDomain := first.baseSet ∩ second.baseSet
  let totalDomain : Set (B × EG) := adjointBundleOverlapDomain (I := IG) first second
  have zeroInput : ContMDiffOn IB (IB.prod 𝓘(ℝ, EG)) ∞
      (fun b : B => (b, (0 : EG))) baseDomain :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have zeroMaps : Set.MapsTo (fun b : B => (b, (0 : EG))) baseDomain totalDomain := by
    intro b hb
    change (b, (0 : EG)) ∈ adjointBundleOverlapDomain (I := IG) first second
    rw [adjointBundleOverlapDomain_eq (I := IG) first second]
    exact ⟨hb, Set.mem_univ _⟩
  have groupOnBase : ContMDiffOn IB IG ∞
      (fun b : B => (principalBundleTransition first second (b, (1 : G))).2) baseDomain := by
    have groupOnTotal := adjointBundleTransitionGroup_contMDiffOn
      smoothBundle first second first_mem second_mem
    simpa [Function.comp_def, totalDomain, baseDomain] using
      groupOnTotal.comp zeroInput zeroMaps
  have composed :=
    (YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv_contMDiff
      (I := IG) (G := G)).comp_contMDiffOn groupOnBase
  simpa [adjointBundleTransitionEquiv, Function.comp_def] using composed

include smoothBundle first_mem second_mem in
/-- The inverse operator-valued transition family is smooth on the same base intersection. -/
theorem adjointBundleTransitionEquiv_symm_contMDiffOn :
    ContMDiffOn IB 𝓘(ℝ, EG →L[ℝ] EG) ∞
      (fun b : B =>
        (adjointBundleTransitionEquiv (IG := IG) first second b).symm.toContinuousLinearMap)
      (first.baseSet ∩ second.baseSet) := by
  let baseDomain := first.baseSet ∩ second.baseSet
  let totalDomain : Set (B × EG) := adjointBundleOverlapDomain (I := IG) first second
  have zeroInput : ContMDiffOn IB (IB.prod 𝓘(ℝ, EG)) ∞
      (fun b : B => (b, (0 : EG))) baseDomain :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have zeroMaps : Set.MapsTo (fun b : B => (b, (0 : EG))) baseDomain totalDomain := by
    intro b hb
    change (b, (0 : EG)) ∈ adjointBundleOverlapDomain (I := IG) first second
    rw [adjointBundleOverlapDomain_eq (I := IG) first second]
    exact ⟨hb, Set.mem_univ _⟩
  have groupOnBase : ContMDiffOn IB IG ∞
      (fun b : B => (principalBundleTransition first second (b, (1 : G))).2) baseDomain := by
    have groupOnTotal := adjointBundleTransitionGroup_contMDiffOn
      smoothBundle first second first_mem second_mem
    simpa [Function.comp_def, totalDomain, baseDomain] using
      groupOnTotal.comp zeroInput zeroMaps
  have composed :=
    (YangMills.Mathematics.lieGroupAdjointCoordinatesEquiv_symm_contMDiff
      (I := IG) (G := G)).comp_contMDiffOn groupOnBase
  simpa [adjointBundleTransitionEquiv, Function.comp_def] using composed

include smoothBundle first_mem second_mem in
/-- The model-coordinate associated transition is smooth on its natural overlap domain. -/
theorem adjointBundleTransitionCoordinates_contMDiffOn :
    ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      (adjointBundleTransitionCoordinates (IG := IG) first second)
      (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG)) := by
  let domain : Set (B × EG) := adjointBundleOverlapDomain (I := IG) first second
  have groupSmooth := adjointBundleTransitionGroup_contMDiffOn
    smoothBundle first second first_mem second_mem
  have actionInput : ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IG.prod 𝓘(ℝ, EG)) ∞
      (fun z : B × EG =>
        ((principalBundleTransition first second (z.1, (1 : G))).2, z.2)) domain :=
    groupSmooth.prodMk contMDiffOn_snd
  have fiberSmooth : ContMDiffOn (IB.prod 𝓘(ℝ, EG)) 𝓘(ℝ, EG) ∞
      (fun z : B × EG =>
        YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
          (principalBundleTransition first second (z.1, (1 : G))).2 z.2) domain := by
    simpa [Function.comp_def] using
      (YangMills.Mathematics.lieGroupAdjointCoordinates_action_contMDiff
        (I := IG) (G := G)).comp_contMDiffOn actionInput
  change ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
    (fun z : B × EG =>
      (z.1, YangMills.Mathematics.lieGroupAdjointCoordinates (I := IG)
        (principalBundleTransition first second (z.1, (1 : G))).2 z.2)) domain
  exact contMDiffOn_fst.prodMk fiberSmooth

set_option backward.isDefEq.respectTransparency false in
/-- On the overlap, the totalized quotient transition agrees exactly with the smooth model-coordinate
formula; smoothness is therefore tied to the previously derived quotient map rather than a surrogate. -/
theorem adjointBundleTransition_eq_coordinates
    (z : B × EG)
    (hz : z ∈ (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG))) :
    adjointBundleTransition (I := IG) bundle first second z =
      adjointBundleTransitionCoordinates (IG := IG) first second z := by
  rw [adjointBundleTransition_eq (I := IG) bundle first second z hz]
  ext <;> rfl

end

end YangMills.Geometry
