/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Weak convergence of finite measures

This file packages weak convergence of genuinely finite measures against explicitly measurable,
bounded continuous real test functions. Finiteness is part of the predicate; probability
normalization remains an obligation of callers. Applications claiming all bounded continuous tests
must separately prove topology/measurability coverage.
-/

namespace YangMills.Mathematics

open Filter MeasureTheory Set

noncomputable section

universe uΩ

/-- A real-valued continuous function carrying an explicit global absolute bound. -/
structure BoundedContinuousRealFunction
    (Ω : Type uΩ) [MeasurableSpace Ω] [TopologicalSpace Ω] where
  toFun : Ω → ℝ
  continuous_toFun : Continuous toFun
  measurable_toFun : Measurable toFun
  bound : ℝ
  abs_le_bound : ∀ ω, |toFun ω| ≤ bound

namespace BoundedContinuousRealFunction

variable {Ω : Type uΩ} [MeasurableSpace Ω] [TopologicalSpace Ω]

/-- On a compact Borel space, every continuous real function canonically supplies the explicit
measurability and global bound required by the weak-convergence test carrier. -/
noncomputable def ofContinuous
    [BorelSpace Ω] [CompactSpace Ω]
    (f : Ω → ℝ) (hf : Continuous f) : BoundedContinuousRealFunction Ω := by
  have bounded : Bornology.IsBounded (f '' (Set.univ : Set Ω)) :=
    (isCompact_univ.image hf).isBounded
  let radius : ℝ := Classical.choose (bounded.subset_closedBall 0)
  have subset : f '' (Set.univ : Set Ω) ⊆ Metric.closedBall (0 : ℝ) radius :=
    Classical.choose_spec (bounded.subset_closedBall 0)
  exact {
    toFun := f
    continuous_toFun := hf
    measurable_toFun := hf.measurable
    bound := radius
    abs_le_bound := fun x => by
      have member : f x ∈ Metric.closedBall (0 : ℝ) radius :=
        subset ⟨x, Set.mem_univ x, rfl⟩
      simpa [Metric.mem_closedBall, Real.dist_eq] using member
  }

@[simp]
theorem ofContinuous_toFun
    [BorelSpace Ω] [CompactSpace Ω]
    (f : Ω → ℝ) (hf : Continuous f) :
    (ofContinuous f hf).toFun = f :=
  rfl

instance : CoeFun (BoundedContinuousRealFunction Ω) (fun _ => Ω → ℝ) :=
  ⟨BoundedContinuousRealFunction.toFun⟩

/-- The constant-one bounded continuous test function. -/
def one : BoundedContinuousRealFunction Ω where
  toFun := fun _ => 1
  continuous_toFun := continuous_const
  measurable_toFun := measurable_const
  bound := 1
  abs_le_bound := fun _ => by norm_num

end BoundedContinuousRealFunction

/-- Weak convergence of genuinely finite measures, tested against every explicitly measurable,
bounded continuous real function. -/
structure WeaklyConvergesFiniteMeasures
    {Ω : Type uΩ} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (sequence : ℕ → Measure Ω) (limit : Measure Ω) : Prop where
  sequence_finite : ∀ stage, sequence stage univ ≠ ⊤
  limit_finite : limit univ ≠ ⊤
  tendsto_integral : ∀ observable : BoundedContinuousRealFunction Ω,
    Tendsto (fun stage => ∫ ω, observable ω ∂sequence stage) atTop
      (nhds (∫ ω, observable ω ∂limit))

namespace WeaklyConvergesFiniteMeasures

variable {Ω : Type uΩ} [MeasurableSpace Ω] [TopologicalSpace Ω]

/-- Weak convergence includes convergence of total-mass test integrals through the constant-one
observable. -/
theorem one_test
    {sequence : ℕ → Measure Ω} {limit : Measure Ω}
    (weak : WeaklyConvergesFiniteMeasures sequence limit) :
    Tendsto (fun stage => ∫ _ : Ω, (1 : ℝ) ∂sequence stage) atTop
      (nhds (∫ _ : Ω, (1 : ℝ) ∂limit)) :=
  weak.tendsto_integral BoundedContinuousRealFunction.one

end WeaklyConvergesFiniteMeasures

end

end YangMills.Mathematics
