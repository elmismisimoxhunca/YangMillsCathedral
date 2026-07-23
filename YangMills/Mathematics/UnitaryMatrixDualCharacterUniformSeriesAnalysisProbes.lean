/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterUniformSeriesAnalysis

/-!
# Hostile probes for analysis of uniformly summable character series
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterUniformSeriesAnalysis
namespace Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- Continuous selected characters map to the exact normalized-Haar `L²` character vectors. -/
theorem exact_continuous_character_toL2
    (q : UnitaryMatrixDual G) :
    normalizedCompactHaarContinuousToL2 G (unitaryMatrixDualContinuousCharacter q) =
      unitaryMatrixDualL2CharacterVector q :=
  normalizedCompactHaarContinuousToL2_unitaryMatrixDualContinuousCharacter q

/-- `L²` analysis recovers every coefficient of a weighted uniformly convergent series. -/
theorem exact_uniform_series_L2_coefficient
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (normalizedCompactHaarContinuousToL2 G
        (unitaryMatrixDualUniformCharacterSeries a)) = a q :=
  unitaryMatrixDualL2CharacterAnalysis_uniformCharacterSeries a h q

/-- The source-facing normalized-Haar integral recovers the exact unchanged coefficient. -/
theorem exact_uniform_series_integral_coefficient
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (q : UnitaryMatrixDual G) :
    (∫ g, star (unitaryMatrixDualCharacter q g) *
      unitaryMatrixDualUniformCharacterSeries a g
      ∂normalizedCompactHaarMeasure G) = a q :=
  normalizedCompactHaar_characterAnalysis_uniformCharacterSeries a h q

/-- Hostile coefficient probe: changing one recovered integral coefficient is contradictory. -/
theorem changed_uniform_series_integral_coefficient_blocked
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (q : UnitaryMatrixDual G) {changed : ℂ} (hchanged : changed ≠ a q)
    (changedCoefficient : (∫ g, star (unitaryMatrixDualCharacter q g) *
      unitaryMatrixDualUniformCharacterSeries a g
      ∂normalizedCompactHaarMeasure G) = changed) : False := by
  apply hchanged
  rw [← changedCoefficient]
  exact normalizedCompactHaar_characterAnalysis_uniformCharacterSeries a h q

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Weighted summability gives vectorwise countable support without making the dual countable. -/
theorem exact_weighted_coefficient_countable_support
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    Set.Countable {q | a q ≠ 0} :=
  countable_setOf_ne_zero_of_summable_characterDimensionWeight a h

/-- Two weighted uniformly convergent character series are equal only if every coefficient agrees. -/
theorem exact_uniform_series_injectivity
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (heq : unitaryMatrixDualUniformCharacterSeries a =
      unitaryMatrixDualUniformCharacterSeries b) :
    a = b :=
  unitaryMatrixDualUniformCharacterSeries_injective a b ha hb heq

/-- Hostile uniqueness probe: equal weighted series with unequal coefficients are contradictory. -/
theorem equal_uniform_series_unequal_coefficients_blocked
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (heq : unitaryMatrixDualUniformCharacterSeries a =
      unitaryMatrixDualUniformCharacterSeries b)
    (hne : a ≠ b) : False :=
  hne (unitaryMatrixDualUniformCharacterSeries_injective a b ha hb heq)

end

end Probes
end UnitaryMatrixDualCharacterUniformSeriesAnalysis
end Mathematics
end YangMills
