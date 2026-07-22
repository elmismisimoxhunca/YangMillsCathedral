/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceBoundaryDerivative

/-!
# Hostile probes for half-space boundary derivatives
-/

namespace YangMills.Mathematics.EuclideanHalfSpaceBoundaryDerivative.Probes

open Set Filter
open scoped Topology

noncomputable section

/-- Exact local half-space preservation produces a genuine local minimum of the target normal
coordinate at the boundary image. -/
theorem exact_normal_coordinate_local_minimum
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0) :
    IsLocalMinOn (fun z => (f z) 0) s x :=
  euclideanHalfSpace_normalCoordinate_isLocalMinOn output_boundary maps_halfSpace

/-- Bidirectional tangent-cone membership forces the derivative into the exact target boundary
hyperplane. -/
theorem exact_bidirectional_tangent_transport
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (tangent : w ∈ posTangentConeAt s x) (neg_tangent : -w ∈ posTangentConeAt s x) :
    (f' w) 0 = 0 :=
  HasFDerivWithinAt.euclideanHalfSpace_mapsTangent hf output_boundary maps_halfSpace
    tangent neg_tangent

/-- A one-sided inward tangent-cone direction cannot acquire a strictly negative target normal
derivative. -/
theorem negative_inward_derivative_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (inward : w ∈ posTangentConeAt s x)
    (wrongNegative : (f' w) 0 < 0) : False :=
  (not_lt_of_ge
    (HasFDerivWithinAt.euclideanHalfSpace_normal_nonneg hf output_boundary maps_halfSpace
      inward)) wrongNegative

/-- A claimed nonzero normal derivative on a bidirectional tangent direction contradicts the exact
Fermat/tangent-cone transport theorem. -/
theorem nonzero_tangent_normal_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (tangent : w ∈ posTangentConeAt s x) (neg_tangent : -w ∈ posTangentConeAt s x)
    (wrongNonzero : (f' w) 0 ≠ 0) : False :=
  wrongNonzero
    (HasFDerivWithinAt.euclideanHalfSpace_mapsTangent hf output_boundary maps_halfSpace
      tangent neg_tangent)

end

end YangMills.Mathematics.EuclideanHalfSpaceBoundaryDerivative.Probes
