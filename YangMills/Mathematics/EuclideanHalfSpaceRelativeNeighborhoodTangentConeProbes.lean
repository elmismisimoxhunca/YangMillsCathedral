/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceRelativeNeighborhoodTangentCone

/-!
# Hostile probes for relative half-space tangent cones
-/

namespace YangMills.Mathematics.EuclideanHalfSpaceRelativeNeighborhoodTangentCone.Probes

open Set Filter
open scoped Manifold Topology

noncomputable section

/-- Every exact boundary-tangent vector is present in both cone directions for any relative
half-space neighborhood. -/
theorem exact_bidirectional_boundary_tangent
    {n : ℕ} [NeZero n]
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (source_nhds : s ∈ 𝓝[Set.range (𝓡∂ n)] x)
    (source_boundary : x 0 = 0) (tangent : w 0 = 0) :
    w ∈ posTangentConeAt s x ∧ -w ∈ posTangentConeAt s x :=
  euclideanHalfSpace_tangent_mem_posTangentConeAt source_nhds source_boundary tangent

/-- The distinguished inward normal is genuinely a one-sided cone direction. -/
theorem exact_inward_normal
    {n : ℕ} [NeZero n]
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (source_nhds : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (source_boundary : x 0 = 0) :
    EuclideanSpace.single 0 1 ∈ posTangentConeAt s x :=
  euclideanHalfSpace_inwardNormal_mem_posTangentConeAt source_nhds source_boundary

/-- A locally half-space-valued derivative on the exact relative source neighborhood cannot send a
boundary-tangent vector to a nonzero target normal component. -/
theorem changed_boundary_tangent_image_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (source_nhds : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (source_boundary : x 0 = 0)
    (target_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (tangent : w 0 = 0) (wrong : (f' w) 0 ≠ 0) : False :=
  wrong (HasFDerivWithinAt.euclideanHalfSpace_maps_boundaryTangent hf source_nhds
    source_boundary target_boundary maps_halfSpace tangent)

/-- A negative image of the distinguished inward normal is incompatible with the exact relative
source geometry and local target-half-space preservation. -/
theorem negative_inward_normal_image_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (source_nhds : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (source_boundary : x 0 = 0)
    (target_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (wrong : (f' (EuclideanSpace.single 0 1)) 0 < 0) : False :=
  (not_lt_of_ge (HasFDerivWithinAt.euclideanHalfSpace_inwardNormal_nonneg hf source_nhds
    source_boundary target_boundary maps_halfSpace)) wrong

end

end YangMills.Mathematics.EuclideanHalfSpaceRelativeNeighborhoodTangentCone.Probes
