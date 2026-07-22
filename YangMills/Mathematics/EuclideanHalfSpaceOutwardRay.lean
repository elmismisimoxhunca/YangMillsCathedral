/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Straight outward rays in a Euclidean half-space

A straight ray based at the boundary of the Euclidean half-space crosses from its interior to its
exterior exactly when the zeroth coordinate of its direction is strictly negative. This isolates
the coordinate geometry needed when analyzing outward tangent vectors on manifolds with boundary.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold

noncomputable section

/-- A straight ray through `x` enters the Euclidean half-space interior in negative time and exits
its exact range in positive time. -/
def IsEuclideanHalfSpaceOutwardRayAt {n : ℕ} [NeZero n]
    (x v : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    (∀ time : ℝ, -radius < time → time < 0 →
      x + time • v ∈ interior (Set.range (𝓡∂ n))) ∧
    (∀ time : ℝ, 0 < time → time < radius →
      x + time • v ∉ Set.range (𝓡∂ n))

/-- At a boundary point, a straight ray crosses outward exactly when its zeroth component points
strictly out of the Euclidean half-space. -/
theorem isEuclideanHalfSpaceOutwardRayAt_iff {n : ℕ} [NeZero n]
    {x v : EuclideanSpace ℝ (Fin n)} (boundary : x 0 = 0) :
    IsEuclideanHalfSpaceOutwardRayAt x v ↔ v 0 < 0 := by
  constructor
  · rintro ⟨radius, radius_pos, _enters, exits⟩
    have exitsAtHalf :=
      exits (radius / 2) (half_pos radius_pos) (half_lt_self radius_pos)
    rw [range_modelWithCornersEuclideanHalfSpace] at exitsAtHalf
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, boundary,
      zero_add, not_le] at exitsAtHalf
    rcases mul_neg_iff.mp exitsAtHalf with outward | impossible
    · exact outward.2
    · exact False.elim
        ((not_lt_of_ge (le_of_lt (half_pos radius_pos))) impossible.1)
  · intro outward
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · intro time _ time_neg
      rw [interior_range_modelWithCornersEuclideanHalfSpace]
      simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, boundary,
        zero_add]
      exact mul_pos_of_neg_of_neg time_neg outward
    · intro time time_pos _
      rw [range_modelWithCornersEuclideanHalfSpace]
      simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, boundary,
        zero_add, not_le]
      exact mul_neg_of_pos_of_neg time_pos outward

/-- A direction with nonnegative zeroth coordinate cannot be outward at a half-space boundary
point. -/
theorem not_isEuclideanHalfSpaceOutwardRayAt_of_nonneg {n : ℕ} [NeZero n]
    {x v : EuclideanSpace ℝ (Fin n)} (boundary : x 0 = 0) (inward : 0 ≤ v 0) :
    ¬ IsEuclideanHalfSpaceOutwardRayAt x v := by
  rw [isEuclideanHalfSpaceOutwardRayAt_iff boundary]
  exact not_lt_of_ge inward

end

end YangMills.Mathematics
