/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceExtendedCoordChange

/-!
# Tangent chain rule for half-space chart transitions

For overlapping atlas charts, the direct tangent coordinate in the second chart is exactly the
within derivative of Mathlib's extended coordinate change applied to the direct tangent coordinate
in the first chart. The transition derivative remains within its exact source.
-/

namespace YangMills.Mathematics

open Set Filter
open scoped Manifold Topology

noncomputable section

/-- The direct tangent coordinate in an overlapping atlas chart is the exact within derivative of
that chart transition applied to the first chart's tangent coordinate. -/
theorem extendedCoordChange_tangent_chainRule
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) 1 M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {x : M}
    (he : e ∈ atlas (EuclideanHalfSpace n) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace n) M)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (v : TangentSpace (𝓡∂ n) x) :
    let φ := (𝓡∂ n).extendCoordChange e e'
    NormedSpace.fromTangentSpace (e'.extend (𝓡∂ n) x)
        (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (e'.extend (𝓡∂ n)) x v) =
      fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
        (NormedSpace.fromTangentSpace (e.extend (𝓡∂ n) x)
          (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (e.extend (𝓡∂ n)) x v)) := by
  let φ := (𝓡∂ n).extendCoordChange e e'
  have hp : e.extend (𝓡∂ n) x ∈ φ.source := by
    simp [φ, hxe, hxe']
  have hφ : MDifferentiableWithinAt
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      φ φ.source (e.extend (𝓡∂ n) x) := by
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    exact (((𝓡∂ n).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he'))
        _ hp).differentiableWithinAt one_ne_zero
  have he_diff : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (e.extend (𝓡∂ n)) x := by
    exact (𝓡∂ n).hasMFDerivAt.comp x
      (mdifferentiableAt_atlas he hxe).hasMFDerivAt |>.mdifferentiableAt
  have hpre : (e.extend (𝓡∂ n)) ⁻¹' φ.source ∈ 𝓝 x := by
    refine mem_of_superset (inter_mem (e.open_source.mem_nhds hxe)
      (e'.open_source.mem_nhds hxe')) ?_
    intro y hy
    simp only [mem_preimage]
    simp [φ, hy.1, hy.2]
  have hcomp := mfderivWithin_comp_of_preimage_mem_nhdsWithin
    (I := (𝓡∂ n)) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (s := (Set.univ : Set M)) (u := φ.source)
    x hφ he_diff.mdifferentiableWithinAt
    (by simpa only [nhdsWithin_univ] using hpre)
    (uniqueMDiffWithinAt_univ (I := (𝓡∂ n)))
  have hlocal : (φ ∘ e.extend (𝓡∂ n)) =ᶠ[𝓝 x] e'.extend (𝓡∂ n) := by
    filter_upwards [e.open_source.mem_nhds hxe, e'.open_source.mem_nhds hxe'] with y hye hye'
    simp [φ, Function.comp_apply, hye]
  have hxvalue : (φ ∘ e.extend (𝓡∂ n)) x = e'.extend (𝓡∂ n) x :=
    hlocal.self_of_nhds
  rw [hxvalue] at hcomp
  have hderiv :
      mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (e'.extend (𝓡∂ n)) x =
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) φ φ.source
          (e.extend (𝓡∂ n) x)).comp
        (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (e.extend (𝓡∂ n)) x) := by
    rw [← hlocal.mfderiv_eq]
    simpa only [mfderivWithin_univ] using hcomp
  change _ = _
  rw [hderiv]
  simp only [mfderivWithin_eq_fderivWithin]
  rfl

end
end YangMills.Mathematics
