/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceOutwardRay

/-!
# Hostile probes for Euclidean half-space outward rays
-/

namespace YangMills.Mathematics.EuclideanHalfSpaceOutwardRay.Probes

open scoped Manifold

noncomputable section

/-- The exact two-sided ray predicate exposes the strict outward coordinate sign. -/
theorem exact_outward_coordinate {n : ℕ} [NeZero n]
    {x v : EuclideanSpace ℝ (Fin n)} (boundary : x 0 = 0) :
    IsEuclideanHalfSpaceOutwardRayAt x v ↔ v 0 < 0 :=
  isEuclideanHalfSpaceOutwardRayAt_iff boundary

/-- A tangent direction along the half-space boundary cannot be substituted for an outward one. -/
theorem tangent_direction_blocked {n : ℕ} [NeZero n]
    {x v : EuclideanSpace ℝ (Fin n)} (boundary : x 0 = 0) (tangent : v 0 = 0) :
    ¬ IsEuclideanHalfSpaceOutwardRayAt x v :=
  not_isEuclideanHalfSpaceOutwardRayAt_of_nonneg boundary (tangent ▸ le_rfl)

/-- A strictly inward direction cannot satisfy the positive-time exit condition. -/
theorem inward_direction_blocked {n : ℕ} [NeZero n]
    {x v : EuclideanSpace ℝ (Fin n)} (boundary : x 0 = 0) (inward : 0 < v 0) :
    ¬ IsEuclideanHalfSpaceOutwardRayAt x v :=
  not_isEuclideanHalfSpaceOutwardRayAt_of_nonneg boundary (le_of_lt inward)

/-- Reversing a genuinely outward direction produces a non-outward direction. -/
theorem reversed_outward_direction_blocked {n : ℕ} [NeZero n]
    {x v : EuclideanSpace ℝ (Fin n)} (boundary : x 0 = 0)
    (outward : IsEuclideanHalfSpaceOutwardRayAt x v) :
    ¬ IsEuclideanHalfSpaceOutwardRayAt x (-v) := by
  apply not_isEuclideanHalfSpaceOutwardRayAt_of_nonneg boundary
  have sign : v 0 < 0 := (isEuclideanHalfSpaceOutwardRayAt_iff boundary).mp outward
  simpa using le_of_lt (neg_pos.mpr sign)

end

end YangMills.Mathematics.EuclideanHalfSpaceOutwardRay.Probes
