/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Transporting densities through measurable equivalences

Mapping a density-weighted measure through a measurable equivalence is the mapped base measure
weighted by the target density, provided the source density is the target density composed with the
equivalence. This is general measure-theoretic infrastructure.
-/

namespace YangMills.Mathematics

open MeasureTheory

namespace MeasurableEquiv

/-- Transport a measurable density through an exact measurable equivalence. -/
theorem map_withDensity_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (equiv : α ≃ᵐ β) (μ : Measure α) (density : β → ENNReal)
    (_density_measurable : Measurable density) :
    Measure.map equiv (μ.withDensity (density ∘ equiv)) =
      (Measure.map equiv μ).withDensity density := by
  ext measurableSet measurableSet_measurable
  rw [equiv.map_apply,
    withDensity_apply _ (equiv.measurable measurableSet_measurable),
    withDensity_apply _ measurableSet_measurable]
  rw [equiv.restrict_map]
  exact (lintegral_map_equiv density equiv).symm

end MeasurableEquiv

end YangMills.Mathematics
