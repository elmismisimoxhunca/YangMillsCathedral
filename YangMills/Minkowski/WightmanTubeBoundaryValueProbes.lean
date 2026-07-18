/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubeBoundaryValue

/-!
# Hostile probes for Wightman tube boundary values

The probes expose the all-direction boundary filter, exact tube approach, genuine integrability,
coherent regularized distributions, and convergence to the selected boundary distribution. No
analytic datum is constructed.
-/

namespace YangMills.Minkowski.WightmanTubeBoundaryValue.Probes

/-- The all-coordinate strict forward-direction domain is open. -/
theorem exact_forward_direction_set_open
    (d : EuclideanDimension) (n : ℕ) :
    IsOpen (wightmanForwardDirectionSet d n) :=
  isOpen_wightmanForwardDirectionSet d n

/-- Positive standard directions exist at every scale. -/
theorem positive_standard_direction_exact
    (d : EuclideanDimension) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    t • standardWightmanForwardDirection d n ∈
      wightmanForwardDirectionSet d n :=
  positive_smul_standardWightmanForwardDirection_mem d n ht

/-- Those strict directions genuinely approach the zero boundary. -/
theorem strict_directions_tend_to_zero
    (d : EuclideanDimension) (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => t • standardWightmanForwardDirection d n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  standardWightmanForwardDirection_tendsto_zero d n

/-- The all-direction boundary filter is nontrivial at every arity. -/
theorem exact_boundary_filter_neBot
    (d : EuclideanDimension) (n : ℕ) :
    (nhdsWithin 0 (wightmanForwardDirectionSet d n)).NeBot :=
  wightmanForwardDirection_nhdsWithin_neBot d n

/-- At positive arity the standard approach uses genuinely nonzero strict directions. -/
theorem positive_arity_standard_direction_ne_zero
    (d : EuclideanDimension) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    t • standardWightmanForwardDirection d n ≠ 0 :=
  positive_smul_standardWightmanForwardDirection_ne_zero d hn ht

/-- Every admissible imaginary direction lands in the exact negative-imaginary tube. -/
theorem exact_approach_point_mem
    {d : EuclideanDimension} {n : ℕ}
    {ξ η : Mathematics.FiniteConfiguration (Spacetime d) n}
    (hη : η ∈ wightmanForwardDirectionSet d n) :
    wightmanTubeApproachPoint ξ η ∈ wightmanBackwardTube d n :=
  wightmanTubeApproachPoint_mem hη

variable
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    (data : WightmanTubeBoundaryValueData d n boundary)

/-- Holomorphy is on the exact source-facing open tube. -/
theorem exact_tube_holomorphy :
    DifferentiableOn ℂ data.tubeFunction (wightmanBackwardTube d n) :=
  data.holomorphic

/-- The regularized integrand is genuinely integrable for every strict direction and Schwartz test. -/
theorem exact_regularized_integrability
    (η : Mathematics.FiniteConfiguration (Spacetime d) n)
    (hη : η ∈ wightmanForwardDirectionSet d n)
    (test : ScalarMinkowskiNPointSchwartzTestFunction d n) :
    MeasureTheory.Integrable
      (fun ξ => data.tubeFunction (wightmanTubeApproachPoint ξ η) * test ξ) :=
  data.approximation_integrable η hη test

/-- Every approximating distribution is exactly the integral of the same tube function. -/
theorem exact_regularized_distribution
    (η : Mathematics.FiniteConfiguration (Spacetime d) n)
    (hη : η ∈ wightmanForwardDirectionSet d n)
    (test : ScalarMinkowskiNPointSchwartzTestFunction d n) :
    data.boundaryApproximation η test =
      ∫ ξ, data.tubeFunction (wightmanTubeApproachPoint ξ η) * test ξ :=
  data.approximation_coherent η hη test

/-- Boundary convergence uses all strict direction tuples tending jointly to zero. -/
theorem exact_distributional_boundary_limit :
    Filter.Tendsto data.boundaryApproximation
      (nhdsWithin 0 (wightmanForwardDirectionSet d n)) (nhds boundary) :=
  data.boundary_tendsto

/-- An unrelated regularized value is rejected against the exact tube integral. -/
theorem disconnected_regularized_value_blocked
    (η : Mathematics.FiniteConfiguration (Spacetime d) n)
    (hη : η ∈ wightmanForwardDirectionSet d n)
    (test : ScalarMinkowskiNPointSchwartzTestFunction d n) (z : ℂ)
    (hmismatch : z ≠
      ∫ ξ, data.tubeFunction (wightmanTubeApproachPoint ξ η) * test ξ) :
    data.boundaryApproximation η test ≠ z := by
  rw [data.approximation_coherent η hη test]
  exact fun h => hmismatch h.symm

end YangMills.Minkowski.WightmanTubeBoundaryValue.Probes
