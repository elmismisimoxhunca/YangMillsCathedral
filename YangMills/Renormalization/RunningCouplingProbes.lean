/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Renormalization.RunningCoupling

/-!
# Hostile probes for perturbative running coupling

The probes expose the exact logarithmic-scale flow, ultraviolet limit, negative cubic beta
asymptotic, and rejection of zero/constant/disconnected surrogates.
-/

namespace YangMills.Renormalization.RunningCoupling.Probes

open Filter Set Topology
open scoped Manifold ContDiff

variable
    {d : EuclideanDimension} {G E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}

/-- The perturbative cubic beta obligation cannot be silently reused in a lower dimension. -/
theorem exact_four_dimensional_scope
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    d = EuclideanDimension.four :=
  data.dimension_eq_four

/-- The same coupling and beta function satisfy the exact flow and ultraviolet limit on the
explicit ultraviolet tail. -/
theorem exact_flow_and_ultraviolet_limit
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    (t : ℝ) (ht : data.ultravioletThreshold < t) :
    HasDerivAt data.runningCoupling
        (data.betaFunction (data.runningCoupling t)) t ∧
      Tendsto data.runningCoupling atTop (nhds 0) :=
  ⟨data.flow_equation t ht, data.ultraviolet_limit⟩

/-- The fixed point and negative cubic leading convention are explicit. -/
theorem exact_beta_leading_asymptotic
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    data.betaFunction 0 = 0 ∧ 0 < data.leadingCoefficient ∧
      Tendsto (fun g => data.betaFunction g / g ^ 3)
        (nhdsWithin 0 (Ioi 0)) (nhds (-data.leadingCoefficient)) :=
  ⟨data.beta_zero, data.leadingCoefficient_pos, data.beta_leading⟩

/-- Positive running coupling prevents a zero-coupling family at finite scale. -/
theorem zero_running_coupling_blocked
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    (t : ℝ) (ht : data.ultravioletThreshold < t) :
    0 < data.runningCoupling t ∧ data.runningCoupling t ≠ 0 :=
  ⟨data.runningCoupling_pos t ht, data.runningCoupling_ne_zero t ht⟩

/-- A fixed positive coupling cannot masquerade as ultraviolet freedom. -/
theorem constant_running_coupling_blocked
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    ¬ ∃ coupling : ℝ, data.runningCoupling = fun _ => coupling :=
  data.runningCoupling_not_constant

/-- The source-facing cubic asymptotic forces actual negative beta values near zero. -/
theorem exact_beta_negative_eventually
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    ∀ᶠ g in nhdsWithin 0 (Ioi 0), data.betaFunction g < 0 :=
  data.beta_negative_eventually

/-- An eventually nonnegative beta function cannot satisfy the accepted leading asymptotic. -/
theorem nonnegative_beta_near_zero_blocked
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    ¬ ∀ᶠ g in nhdsWithin 0 (Ioi 0), 0 ≤ data.betaFunction g := by
  intro nonnegative
  have contradiction := data.beta_negative_eventually.and nonnegative
  rcases contradiction.exists with ⟨g, negative, nonnegative⟩
  exact (not_lt_of_ge nonnegative) negative

/-- A derivative disconnected from the same beta function is rejected by derivative uniqueness. -/
theorem disconnected_flow_derivative_blocked
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    (t replacement : ℝ) (ht : data.ultravioletThreshold < t)
    (mismatch : replacement ≠ data.betaFunction (data.runningCoupling t)) :
    ¬ HasDerivAt data.runningCoupling replacement t := by
  intro replacementDerivative
  exact mismatch (replacementDerivative.unique (data.flow_equation t ht))

end YangMills.Renormalization.RunningCoupling.Probes
