/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubePolynomialGrowth

/-!
# Hostile probes for Wightman tube polynomial growth

The probes expose compact-direction uniformity, nonnegative constants, a concrete standard
direction bound, and pointwise validity of the extracted compact-set certificate. No analytic datum is constructed.
-/

namespace YangMills.Minkowski.WightmanTubePolynomialGrowth.Probes

variable
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    (data : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary)

/-- The exact radial growth condition is present on the exact tube function. -/
theorem exact_polynomial_growth :
    IsPolynomiallyBoundedOnWightmanTube d n data.tubeFunction :=
  data.polynomially_bounded

/-- Every compact strict direction set receives one uniform nonnegative polynomial bound. -/
theorem exact_compact_direction_bound
    (K : Set (Mathematics.FiniteConfiguration (Spacetime d) n))
    (hK : IsCompact K) (hsub : K ⊆ wightmanForwardDirectionSet d n) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ ξ : Mathematics.FiniteConfiguration (Spacetime d) n,
      ∀ η ∈ K,
        ‖data.tubeFunction (wightmanTubeApproachPoint ξ η)‖ ≤
          C * (1 + ‖ξ‖) ^ N :=
  data.polynomially_bounded K hK hsub

/-- The explicit unit-time direction has a concrete polynomial bound. -/
theorem standard_direction_bound :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ ξ : Mathematics.FiniteConfiguration (Spacetime d) n,
        ‖data.tubeFunction
            (wightmanTubeApproachPoint ξ (standardWightmanForwardDirection d n))‖ ≤
          C * (1 + ‖ξ‖) ^ N :=
  data.singleton_direction_bound (standardWightmanForwardDirection d n) (by
    simpa using
      (positive_smul_standardWightmanForwardDirection_mem d n (t := 1) (by norm_num)))

/-- The certified uniform compact-set bound cannot be undersized at any covered point. -/
theorem certified_compact_bound_not_undersized
    (K : Set (Mathematics.FiniteConfiguration (Spacetime d) n))
    (hK : IsCompact K) (hsub : K ⊆ wightmanForwardDirectionSet d n) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ ξ : Mathematics.FiniteConfiguration (Spacetime d) n,
      ∀ η ∈ K,
        ¬ C * (1 + ‖ξ‖) ^ N <
          ‖data.tubeFunction (wightmanTubeApproachPoint ξ η)‖ := by
  rcases data.polynomially_bounded K hK hsub with ⟨C, N, hC, hbound⟩
  exact ⟨C, N, hC, fun ξ η hη => not_lt_of_ge (hbound ξ η hη)⟩

/-- The strengthened data retains the exact all-direction distributional boundary limit. -/
theorem exact_boundary_limit_retained :
    Filter.Tendsto data.boundaryApproximation
      (nhdsWithin 0 (wightmanForwardDirectionSet d n)) (nhds boundary) :=
  data.boundary_tendsto

end YangMills.Minkowski.WightmanTubePolynomialGrowth.Probes
