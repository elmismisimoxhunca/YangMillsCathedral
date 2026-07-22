/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceChartTangentChainRule

/-!
# Hostile probes for the half-space chart tangent chain rule
-/

namespace YangMills.Mathematics.EuclideanHalfSpaceChartTangentChainRule.Probes

open Set Filter
open scoped Manifold Topology

noncomputable section

/-- The second direct chart tangent is the exact transition-within derivative of the first. -/
theorem exact_direct_tangent_transport
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]
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
            (e.extend (𝓡∂ n)) x v)) :=
  extendedCoordChange_tangent_chainRule he he' hxe hxe' v

/-- An unrelated replacement for the transported tangent is rejected by the exact chain rule. -/
theorem changed_direct_tangent_blocked
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {x : M}
    (he : e ∈ atlas (EuclideanHalfSpace n) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace n) M)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source)
    (v : TangentSpace (𝓡∂ n) x)
    (wrong : EuclideanSpace ℝ (Fin n))
    (different : wrong ≠
      NormedSpace.fromTangentSpace (e'.extend (𝓡∂ n) x)
        (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (e'.extend (𝓡∂ n)) x v))
    (claimed :
      let φ := (𝓡∂ n).extendCoordChange e e'
      wrong = fderivWithin ℝ φ φ.source (e.extend (𝓡∂ n) x)
        (NormedSpace.fromTangentSpace (e.extend (𝓡∂ n) x)
          (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (e.extend (𝓡∂ n)) x v))) : False := by
  apply different
  rw [extendedCoordChange_tangent_chainRule he he' hxe hxe' v]
  exact claimed

end

end YangMills.Mathematics.EuclideanHalfSpaceChartTangentChainRule.Probes
