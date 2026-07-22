/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.MeasurableEquivWithDensity

/-!
# Probes for measurable-equivalence density transport
-/

namespace YangMills.Mathematics.MeasurableEquivWithDensity.Probes

open MeasureTheory

universe uα uβ

variable {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]

/-- The exact source density is composition with the same equivalence, and the target base measure
is the map of the same source measure. -/
theorem exact_density_transport
    (equiv : α ≃ᵐ β) (μ : Measure α) (density : β → ENNReal)
    (density_measurable : Measurable density) :
    Measure.map equiv (μ.withDensity (density ∘ equiv)) =
      (Measure.map equiv μ).withDensity density :=
  MeasurableEquiv.map_withDensity_comp equiv μ density density_measurable

/-- An unrelated target measure cannot replace the exact transported density law. -/
theorem unrelated_target_measure_blocked
    (equiv : α ≃ᵐ β) (μ : Measure α) (density : β → ENNReal)
    (density_measurable : Measurable density) (wrong : Measure β)
    (different : wrong ≠ (Measure.map equiv μ).withDensity density)
    (claimed : Measure.map equiv (μ.withDensity (density ∘ equiv)) = wrong) : False := by
  apply different
  rw [← claimed]
  exact MeasurableEquiv.map_withDensity_comp equiv μ density density_measurable

/-- Changing the source density cannot preserve the exact target law when the resulting source
weighted measure is genuinely different. -/
theorem changed_source_density_blocked
    (equiv : α ≃ᵐ β) (μ : Measure α) (density : β → ENNReal)
    (density_measurable : Measurable density) (wrongDensity : α → ENNReal)
    (different : μ.withDensity wrongDensity ≠ μ.withDensity (density ∘ equiv))
    (claimed : Measure.map equiv (μ.withDensity wrongDensity) =
      (Measure.map equiv μ).withDensity density) : False := by
  apply different
  have exactTarget := MeasurableEquiv.map_withDensity_comp
    equiv μ density density_measurable
  have mappedEquality := claimed.trans exactTarget.symm
  have mappedBack := congrArg (Measure.map equiv.symm) mappedEquality
  simpa only [equiv.map_symm_map] using mappedBack

end YangMills.Mathematics.MeasurableEquivWithDensity.Probes
