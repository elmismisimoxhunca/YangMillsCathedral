/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceRelativeNeighborhoodTangentCone

/-!
# Boundary derivatives of extended coordinate changes

For two overlapping atlas charts on a manifold modeled on a Euclidean half-space, the exact within
derivative of Mathlib's extended coordinate change preserves the boundary tangent hyperplane and
carries the distinguished inward normal to a vector with strictly positive normal coordinate.
Consequently it preserves the exact two-sided straight outward-ray predicate.
-/

namespace YangMills.Mathematics

open Set Filter
open scoped Manifold Topology

noncomputable section

/-- The exact extended-coordinate-change derivative preserves boundary tangents and has strictly
positive inward-normal multiplier at a boundary coordinate. -/
theorem extendedCoordChange_boundary_derivative
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) 1 M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {x : M}
    (he : e ∈ atlas (EuclideanHalfSpace n) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace n) M)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (source_boundary : (e.extend (𝓡∂ n) x) 0 = 0)
    (target_boundary : (e'.extend (𝓡∂ n) x) 0 = 0) :
    let φ := (𝓡∂ n).extendCoordChange e e'
    let D := fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
    (∀ w, w 0 = 0 → (D w) 0 = 0) ∧
      0 < (D (EuclideanSpace.single 0 1)) 0 := by
  let φ := (𝓡∂ n).extendCoordChange e e'
  let p := e.extend (𝓡∂ n) x
  let D := fderivWithin ℝ φ φ.source p
  have hp : p ∈ φ.source := by
    simp [p, φ, hxe, hxe']
  have hφ : ContDiffOn ℝ 1 φ φ.source :=
    (𝓡∂ n).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  have hD : HasFDerivWithinAt φ D φ.source p := by
    exact ((hφ p hp).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have source_nhds : φ.source ∈ 𝓝[Set.range (𝓡∂ n)] p := by
    exact (𝓡∂ n).extendCoordChange_source_mem_nhdsWithin' hxe hxe'
  have image_boundary : (φ p) 0 = 0 := by
    simpa [φ, p, hxe] using target_boundary
  have maps_halfSpace : ∀ᶠ z in 𝓝[φ.source] p, 0 ≤ (φ z) 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzt : φ z ∈ φ.target := φ.map_source hz
    have hz' : φ z ∈ Set.range (𝓡∂ n) := by
      rw [(𝓡∂ n).extendCoordChange_target] at hzt
      exact Set.image_subset_range _ _ hzt
    rw [range_modelWithCornersEuclideanHalfSpace] at hz'
    exact hz'
  have maps_tangent : ∀ w, w 0 = 0 → (D w) 0 = 0 := by
    intro w hw
    exact HasFDerivWithinAt.euclideanHalfSpace_maps_boundaryTangent
      hD source_nhds source_boundary image_boundary maps_halfSpace hw
  have normal_nonneg : 0 ≤ (D (EuclideanSpace.single 0 1)) 0 :=
    HasFDerivWithinAt.euclideanHalfSpace_inwardNormal_nonneg
      hD source_nhds source_boundary image_boundary maps_halfSpace
  have D_surjective : Function.Surjective D := by
    exact ((𝓡∂ n).isInvertible_fderivWithin_extendCoordChange
      (n := (1 : WithTop ℕ∞)) (by norm_num)
      (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he') hp).surjective
  exact ⟨maps_tangent,
    ContinuousLinearMap.euclideanHalfSpace_normal_pos_of_surjective D maps_tangent
      normal_nonneg D_surjective⟩

/-- The exact extended-coordinate-change within derivative preserves the full two-sided outward-ray
predicate between boundary chart coordinates. -/
theorem extendedCoordChange_preserves_outwardRay
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) 1 M]
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
    IsEuclideanHalfSpaceOutwardRayAt (e'.extend (𝓡∂ n) x) (D v) := by
  let φ := (𝓡∂ n).extendCoordChange e e'
  let D := fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
  change IsEuclideanHalfSpaceOutwardRayAt (e'.extend (𝓡∂ n) x) (D v)
  obtain ⟨maps_tangent, normal_pos⟩ :=
    extendedCoordChange_boundary_derivative he he' hxe hxe' source_boundary target_boundary
  rw [isEuclideanHalfSpaceOutwardRayAt_iff target_boundary]
  rw [isEuclideanHalfSpaceOutwardRayAt_iff source_boundary] at outward
  exact ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg
    D maps_tangent normal_pos outward

end
end YangMills.Mathematics
