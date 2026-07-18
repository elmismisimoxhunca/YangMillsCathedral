/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Dimensions
import YangMills.Geometry.LieGroup
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Pure Yang–Mills perturbative running coupling

Gross–Wilczek and Politzer formulate asymptotic freedom through a renormalization-group running
coupling and a beta function with negative leading cubic coefficient. This module chooses the
dimensionless logarithmic scale `t = log (μ/μ₀)`, so the flow equation is
`g'(t) = β(g(t))` and the ultraviolet limit is `t → +∞`.

Only a supplied open ultraviolet tail is constrained; no infrared behavior is constrained. The positive
leading coefficient is left explicit because its numerical value depends on coupling, Lie-algebra,
adjoint-Casimir, and invariant-form normalization conventions not yet connected in this project.
The data are indexed by the exact compact-simple gauge-group certificate but currently encode only
the universal sign normal form, not the actual group-dependent one-loop coefficient. No perturbative
series, observable asymptotic, quantum theory, or mass gap is constructed.
-/

namespace YangMills.Renormalization

open Filter Set Topology
open scoped Manifold ContDiff

/-- Preliminary four-dimensional pure-gauge asymptotic-freedom normal form on a logarithmic
ultraviolet scale. -/
structure PureYangMillsAsymptoticFreedomData
    (d : EuclideanDimension)
    {G E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    (gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E) where
  /-- The cubic beta normal form is explicitly a four-dimensional obligation. -/
  dimension_eq_four : d = EuclideanDimension.four
  /-- Beginning of the logarithmic ultraviolet tail on which perturbative flow is required. -/
  ultravioletThreshold : ℝ
  /-- Running coupling on logarithmic scale; values below the threshold are deliberately
  unconstrained. -/
  runningCoupling : ℝ → ℝ
  runningCoupling_pos : ∀ t, ultravioletThreshold < t → 0 < runningCoupling t
  /-- Beta function in the convention `dg/dt = β(g)`. -/
  betaFunction : ℝ → ℝ
  /-- The free ultraviolet point is a beta-function fixed point. -/
  beta_zero : betaFunction 0 = 0
  /-- Exact renormalization-group flow only on the designated ultraviolet tail. -/
  flow_equation : ∀ t, ultravioletThreshold < t →
    HasDerivAt runningCoupling (betaFunction (runningCoupling t)) t
  /-- Ultraviolet freedom: the same running coupling tends to zero at high logarithmic scale. -/
  ultraviolet_limit : Tendsto runningCoupling atTop (nhds 0)
  /-- Positive coefficient in the convention `β(g) = -b₀ g³ + o(g³)`. -/
  leadingCoefficient : ℝ
  leadingCoefficient_pos : 0 < leadingCoefficient
  /-- Exact leading small-positive-coupling beta asymptotic. -/
  beta_leading : Tendsto (fun g => betaFunction g / g ^ 3)
    (nhdsWithin 0 (Ioi 0)) (nhds (-leadingCoefficient))

/-- The running coupling is genuinely nonzero throughout the designated ultraviolet tail. -/
theorem PureYangMillsAsymptoticFreedomData.runningCoupling_ne_zero
    {d : EuclideanDimension} {G E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup)
    (t : ℝ) (ht : data.ultravioletThreshold < t) :
    data.runningCoupling t ≠ 0 :=
  ne_of_gt (data.runningCoupling_pos t ht)

/-- The leading beta asymptotic forces beta to be negative at sufficiently small positive coupling. -/
theorem PureYangMillsAsymptoticFreedomData.beta_negative_eventually
    {d : EuclideanDimension} {G E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    ∀ᶠ g in nhdsWithin 0 (Ioi 0), data.betaFunction g < 0 := by
  have limit_negative : -data.leadingCoefficient < 0 :=
    neg_neg_of_pos data.leadingCoefficient_pos
  have ratio_negative : ∀ᶠ g in nhdsWithin 0 (Ioi 0),
      data.betaFunction g / g ^ 3 < 0 :=
    data.beta_leading.eventually (Iio_mem_nhds limit_negative)
  filter_upwards [ratio_negative, self_mem_nhdsWithin] with g hratio hg
  rcases (div_neg_iff.mp hratio) with impossible | negative
  · exact (not_lt_of_ge (le_of_lt (pow_pos hg 3)) impossible.2).elim
  · exact negative.1

/-- A scale-independent positive coupling cannot satisfy the ultraviolet-tail limit. -/
theorem PureYangMillsAsymptoticFreedomData.runningCoupling_not_constant
    {d : EuclideanDimension} {G E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    (data : PureYangMillsAsymptoticFreedomData d gaugeGroup) :
    ¬ ∃ coupling : ℝ, data.runningCoupling = fun _ => coupling := by
  rintro ⟨coupling, equality⟩
  have constantLimit : Tendsto (fun _ : ℝ => coupling) atTop (nhds coupling) :=
    tendsto_const_nhds
  have ultraviolet := data.ultraviolet_limit
  rw [equality] at ultraviolet
  have coupling_zero : coupling = 0 :=
    tendsto_nhds_unique constantLimit ultraviolet
  have threshold_lt : data.ultravioletThreshold < data.ultravioletThreshold + 1 := by
    linarith
  have positive := data.runningCoupling_pos (data.ultravioletThreshold + 1) threshold_lt
  rw [show data.runningCoupling (data.ultravioletThreshold + 1) = coupling from
      congrFun equality (data.ultravioletThreshold + 1),
    coupling_zero] at positive
  exact lt_irrefl 0 positive

end YangMills.Renormalization
