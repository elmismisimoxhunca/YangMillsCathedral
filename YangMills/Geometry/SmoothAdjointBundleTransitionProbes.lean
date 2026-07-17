/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothAdjointBundleTransition

/-!
# Hostile probes for smooth adjoint-bundle overlap transitions
-/

namespace YangMills.Geometry.Probes

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
/-- The group-valued overlap coordinate cannot fail smoothness on the associated domain. -/
theorem nonsmooth_adjointBundle_transitionGroup_blocked
    (nonsmooth : ¬ContMDiffOn (IB.prod 𝓘(ℝ, EG)) IG ∞
      (fun z : B × EG =>
        (principalBundleTransition first second (z.1, (1 : G))).2)
      (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG))) : False :=
  nonsmooth (adjointBundleTransitionGroup_contMDiffOn
    smoothBundle first second first_mem second_mem)

include smoothBundle first_mem second_mem in
/-- The exact model-coordinate fiberwise-adjoint transition cannot fail smoothness. -/
theorem nonsmooth_adjointBundle_transitionCoordinates_blocked
    (nonsmooth : ¬ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      (adjointBundleTransitionCoordinates (IG := IG) first second)
      (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG))) : False :=
  nonsmooth (adjointBundleTransitionCoordinates_contMDiffOn
    smoothBundle first second first_mem second_mem)

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness cannot be proved for a disconnected surrogate while the quotient transition uses a
different map: the two maps agree pointwise on the exact overlap. -/
theorem disconnected_smooth_adjointBundle_transition_blocked
    (z : B × EG)
    (hz : z ∈ (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG)))
    (mismatch : adjointBundleTransition (I := IG) bundle first second z ≠
      adjointBundleTransitionCoordinates (IG := IG) first second z) : False :=
  mismatch (adjointBundleTransition_eq_coordinates first second z hz)

end

end YangMills.Geometry.Probes
