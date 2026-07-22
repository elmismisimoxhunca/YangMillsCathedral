/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceExtendedCoordChange

/-!
# Hostile probes for half-space extended coordinate changes
-/

namespace YangMills.Mathematics.EuclideanHalfSpaceExtendedCoordChange.Probes

open Set Filter
open scoped Manifold Topology

noncomputable section

/-- The actual extended-coordinate-change derivative carries both exact boundary-linear facts. -/
theorem exact_boundary_derivative
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {x : M}
    (he : e ∈ atlas (EuclideanHalfSpace n) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace n) M)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (source_boundary : (e.extend (𝓡∂ n) x) 0 = 0)
    (target_boundary : (e'.extend (𝓡∂ n) x) 0 = 0) :
    let φ := (𝓡∂ n).extendCoordChange e e'
    let D := fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
    (∀ w, w 0 = 0 → (D w) 0 = 0) ∧
      0 < (D (EuclideanSpace.single 0 1)) 0 :=
  extendedCoordChange_boundary_derivative he he' hxe hxe' source_boundary target_boundary

/-- A zero normal multiplier is incompatible with the actual invertible atlas transition. -/
theorem zero_actual_normal_multiplier_blocked
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {x : M}
    (he : e ∈ atlas (EuclideanHalfSpace n) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace n) M)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (source_boundary : (e.extend (𝓡∂ n) x) 0 = 0)
    (target_boundary : (e'.extend (𝓡∂ n) x) 0 = 0)
    (wrong :
      let φ := (𝓡∂ n).extendCoordChange e e'
      let D := fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
      (D (EuclideanSpace.single 0 1)) 0 = 0) : False := by
  let φ := (𝓡∂ n).extendCoordChange e e'
  let D := fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
  have positive := (extendedCoordChange_boundary_derivative he he' hxe hxe'
    source_boundary target_boundary).2
  exact (ne_of_gt positive) wrong

/-- The full two-sided outward-ray predicate is transported by the actual within derivative, not by
an unrelated linear map. -/
theorem exact_actual_outward_transport
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {x : M}
    (he : e ∈ atlas (EuclideanHalfSpace n) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace n) M)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (source_boundary : (e.extend (𝓡∂ n) x) 0 = 0)
    (target_boundary : (e'.extend (𝓡∂ n) x) 0 = 0)
    {v : EuclideanSpace ℝ (Fin n)}
    (outward : IsEuclideanHalfSpaceOutwardRayAt (e.extend (𝓡∂ n) x) v) :
    let φ := (𝓡∂ n).extendCoordChange e e'
    let D := fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
    IsEuclideanHalfSpaceOutwardRayAt (e'.extend (𝓡∂ n) x) (D v) :=
  extendedCoordChange_preserves_outwardRay he he' hxe hxe'
    source_boundary target_boundary outward

end

end YangMills.Mathematics.EuclideanHalfSpaceExtendedCoordChange.Probes
