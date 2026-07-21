/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.WeakMeasureConvergence

namespace YangMills.Mathematics.WeakMeasureConvergence.Probes

open Filter MeasureTheory

noncomputable section

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω] [TopologicalSpace Ω]

/-- Weak convergence quantifies over the constant-one mass test. -/
theorem includes_mass_test
    {sequence : ℕ → Measure Ω} {limit : Measure Ω}
    (weak : WeaklyConvergesFiniteMeasures sequence limit) :
    Tendsto (fun stage => ∫ _ : Ω, (1 : ℝ) ∂sequence stage) atTop
      (nhds (∫ _ : Ω, (1 : ℝ) ∂limit)) :=
  weak.one_test

/-- Every member of the sequence and the limit are genuinely finite. -/
theorem exact_finiteness
    {sequence : ℕ → Measure Ω} {limit : Measure Ω}
    (weak : WeaklyConvergesFiniteMeasures sequence limit) :
    (∀ stage, sequence stage Set.univ ≠ ⊤) ∧ limit Set.univ ≠ ⊤ :=
  ⟨weak.sequence_finite, weak.limit_finite⟩

/-- A purported weak convergence that fails one bounded continuous measurable test is rejected. -/
theorem failed_test_blocked
    {sequence : ℕ → Measure Ω} {limit : Measure Ω}
    (weak : WeaklyConvergesFiniteMeasures sequence limit)
    (observable : BoundedContinuousRealFunction Ω)
    (failed : ¬ Tendsto (fun stage => ∫ ω, observable ω ∂sequence stage) atTop
      (nhds (∫ ω, observable ω ∂limit))) : False :=
  failed (weak.tendsto_integral observable)

end

end YangMills.Mathematics.WeakMeasureConvergence.Probes
