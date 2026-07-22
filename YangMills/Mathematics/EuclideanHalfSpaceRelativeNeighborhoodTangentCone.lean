/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceBoundaryDerivative

/-!
# Tangent cones of relative half-space neighborhoods

Every affine direction whose positive ray remains in a Euclidean half-space belongs to the positive
tangent cone of any relative neighborhood of its base point. At a boundary point this puts every
boundary-tangent vector and its negative in the cone, while the distinguished inward normal belongs
one-sidedly. These are the exact source-cone hypotheses needed by the boundary derivative results.
-/

namespace YangMills.Mathematics

open Set Filter
open scoped Manifold Topology

noncomputable section

/-- Every direction whose positive affine ray stays in the half-space belongs to the positive
tangent cone of any relative neighborhood of the boundary point. -/
theorem mem_posTangentConeAt_of_mem_nhdsWithin_euclideanHalfSpace
    {n : ℕ} [NeZero n]
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ 𝓝[Set.range (𝓡∂ n)] x)
    (ray : ∀ t : ℝ, 0 < t → x + t • w ∈ Set.range (𝓡∂ n)) :
    w ∈ posTangentConeAt s x := by
  apply mem_posTangentConeAt_of_frequently_mem
  have continuous_line : Tendsto (fun t : ℝ => x + t • w) (𝓝 (0 : ℝ)) (𝓝 x) := by
    have hcont : ContinuousAt (fun t : ℝ => x + t • w) 0 := by fun_prop
    change Tendsto (fun t : ℝ => x + t • w) (𝓝 (0 : ℝ))
      (𝓝 ((fun t : ℝ => x + t • w) 0)) at hcont
    simpa using hcont
  have line_tendsto : Tendsto (fun t : ℝ => x + t • w) (𝓝[>] (0 : ℝ))
      (𝓝[Set.range (𝓡∂ n)] x) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨continuous_line.mono_left inf_le_left, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ray t ht
  exact (line_tendsto.eventually hs).frequently

/-- At a Euclidean-half-space boundary point, every boundary-tangent vector is bidirectional in
the positive tangent cone of any relative neighborhood. -/
theorem euclideanHalfSpace_tangent_mem_posTangentConeAt
    {n : ℕ} [NeZero n]
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (boundary : x 0 = 0) (tangent : w 0 = 0) :
    w ∈ posTangentConeAt s x ∧ -w ∈ posTangentConeAt s x := by
  constructor
  · apply mem_posTangentConeAt_of_mem_nhdsWithin_euclideanHalfSpace hs
    intro t ht
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp [boundary, tangent]
  · apply mem_posTangentConeAt_of_mem_nhdsWithin_euclideanHalfSpace hs
    intro t ht
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp [boundary, tangent]

/-- The distinguished inward normal belongs to the positive tangent cone of every relative
neighborhood of a Euclidean-half-space boundary point. -/
theorem euclideanHalfSpace_inwardNormal_mem_posTangentConeAt
    {n : ℕ} [NeZero n]
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (boundary : x 0 = 0) :
    EuclideanSpace.single 0 1 ∈ posTangentConeAt s x := by
  apply mem_posTangentConeAt_of_mem_nhdsWithin_euclideanHalfSpace hs
  intro t ht
  rw [range_modelWithCornersEuclideanHalfSpace]
  simp [boundary, EuclideanSpace.single, le_of_lt ht]

/-- For a within derivative on a relative half-space neighborhood, boundary-tangent vectors are
sent into the target boundary hyperplane whenever the map is locally target-half-space-valued. -/
theorem HasFDerivWithinAt.euclideanHalfSpace_maps_boundaryTangent
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (source_nhds : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (source_boundary : x 0 = 0)
    (target_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (tangent : w 0 = 0) :
    (f' w) 0 = 0 := by
  obtain ⟨forward, reverse⟩ :=
    euclideanHalfSpace_tangent_mem_posTangentConeAt source_nhds source_boundary tangent
  exact HasFDerivWithinAt.euclideanHalfSpace_mapsTangent hf target_boundary maps_halfSpace
    forward reverse

/-- Under the same exact relative-neighborhood hypotheses, the distinguished inward normal has
nonnegative target normal derivative. -/
theorem HasFDerivWithinAt.euclideanHalfSpace_inwardNormal_nonneg
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (source_nhds : s ∈ 𝓝[Set.range (𝓡∂ n)] x) (source_boundary : x 0 = 0)
    (target_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0) :
    0 ≤ (f' (EuclideanSpace.single 0 1)) 0 := by
  exact HasFDerivWithinAt.euclideanHalfSpace_normal_nonneg hf target_boundary maps_halfSpace
    (euclideanHalfSpace_inwardNormal_mem_posTangentConeAt source_nhds source_boundary)

end

end YangMills.Mathematics
