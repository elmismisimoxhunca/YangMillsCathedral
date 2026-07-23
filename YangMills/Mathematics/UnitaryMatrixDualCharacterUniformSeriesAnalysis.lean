/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterBessel
import YangMills.Mathematics.UnitaryMatrixDualCharacterUniformSeries

/-!
# Fourier analysis of uniformly summable selected-character series

For coefficients satisfying the exact weighted premise

`Summable (fun q => ‖a q‖ * dim(q))`,

the uniformly convergent continuous-central character series has normalized-Haar character
coefficient exactly `a q` for every selected class `q`. Equivalently,

`∫ conj(χ_q) (∑ r, a_r χ_r) dμ_H = a_q`.

Thus weighted uniformly convergent character series have a justified infinite coefficient-recovery
and uniqueness theorem. Their coefficient support is automatically countable, vector by vector,
without proving that the whole selected dual is countable.

This is not inversion of an arbitrary continuous or `L²` function and assumes no Peter–Weyl
completeness, Casimir spectrum, or heat-kernel summability.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- Mapping one continuous selected character into normalized-Haar `L²` gives the previously defined
unit character vector exactly. -/
theorem normalizedCompactHaarContinuousToL2_unitaryMatrixDualContinuousCharacter
    (q : UnitaryMatrixDual G) :
    normalizedCompactHaarContinuousToL2 G (unitaryMatrixDualContinuousCharacter q) =
      unitaryMatrixDualL2CharacterVector q := by
  rw [unitaryMatrixDualL2CharacterVector]
  change normalizedCompactHaarContinuousToL2 G (unitaryMatrixDualContinuousCharacter q) =
    normalizedCompactHaarContinuousToL2 G
      ((unitaryMatrixDualCentralCharacterSynthesis G (Finsupp.single q 1) :
        continuousCentralFunctionStarSubalgebra G) : C(G, ℂ))
  apply congrArg (normalizedCompactHaarContinuousToL2 G)
  ext g
  rw [unitaryMatrixDualCentralCharacterSynthesis_apply,
    unitaryMatrixDualCharacterSynthesis_single]
  simp [unitaryMatrixDualContinuousCharacter]

/-- Exact coefficient recovery: normalized-Haar `L²` analysis of the weighted uniformly convergent
series returns the original coefficient. -/
theorem unitaryMatrixDualL2CharacterAnalysis_uniformCharacterSeries
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (normalizedCompactHaarContinuousToL2 G
        (unitaryMatrixDualUniformCharacterSeries a)) = a q := by
  have hsC := summable_unitaryMatrixDualContinuousCharacter_smul a h
  have hsL2 : Summable (fun r => normalizedCompactHaarContinuousToL2 G
      (a r • unitaryMatrixDualContinuousCharacter r)) := by
    change Summable ((normalizedCompactHaarContinuousToL2 G) ∘
      fun r => a r • unitaryMatrixDualContinuousCharacter r)
    exact hsC.map (normalizedCompactHaarContinuousToL2 G)
      (normalizedCompactHaarContinuousToL2 G).continuous
  unfold unitaryMatrixDualUniformCharacterSeries
  rw [(normalizedCompactHaarContinuousToL2 G).map_tsum hsC]
  rw [(unitaryMatrixDualL2CharacterAnalysis q).map_tsum hsL2]
  rw [tsum_eq_single q]
  · rw [map_smul,
      normalizedCompactHaarContinuousToL2_unitaryMatrixDualContinuousCharacter,
      map_smul]
    change a q * unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterVector q) = a q
    rw [unitaryMatrixDualL2CharacterAnalysis, innerSL_apply_apply,
      inner_self_eq_norm_sq_to_K, norm_unitaryMatrixDualL2CharacterVector]
    simp
  · intro r hrq
    rw [map_smul,
      normalizedCompactHaarContinuousToL2_unitaryMatrixDualContinuousCharacter,
      map_smul]
    change a r * unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterVector r) = 0
    have horth := (orthonormal_unitaryMatrixDualL2CharacterVector (G := G)).inner_eq_zero
      (Ne.symm hrq)
    rw [unitaryMatrixDualL2CharacterAnalysis, innerSL_apply_apply, horth]
    simp

/-- Source-facing coefficient recovery as the exact normalized-Haar character integral. -/
theorem normalizedCompactHaar_characterAnalysis_uniformCharacterSeries
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (q : UnitaryMatrixDual G) :
    (∫ g, star (unitaryMatrixDualCharacter q g) *
      unitaryMatrixDualUniformCharacterSeries a g
      ∂normalizedCompactHaarMeasure G) = a q := by
  change (∫ g, star (unitaryMatrixDualCharacter q g) *
    ((unitaryMatrixDualUniformCentralCharacterSeries a h : C(G, ℂ)) g)
    ∂normalizedCompactHaarMeasure G) = a q
  rw [← unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral
    (unitaryMatrixDualUniformCentralCharacterSeries a h) q]
  change unitaryMatrixDualL2CharacterAnalysis q
    (normalizedCompactHaarContinuousToL2 G
      (unitaryMatrixDualUniformCharacterSeries a)) = a q
  exact unitaryMatrixDualL2CharacterAnalysis_uniformCharacterSeries a h q

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Every weighted-summable coefficient family has at most countable nonzero support, without global
selected-dual countability. -/
theorem countable_setOf_ne_zero_of_summable_characterDimensionWeight
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    Set.Countable {q | a q ≠ 0} := by
  apply h.countable_support.mono
  intro q hq
  change ‖a q‖ * (unitaryMatrixDualDimension q : ℝ) ≠ 0
  apply mul_ne_zero
  · exact norm_ne_zero_iff.mpr hq
  · exact_mod_cast (unitaryMatrixDualRepresentative q).dimension_pos.ne'

/-- Weighted uniformly convergent selected-character synthesis is injective on its exact domain. -/
theorem unitaryMatrixDualUniformCharacterSeries_injective
    (a b : UnitaryMatrixDual G → ℂ)
    (ha : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (heq : unitaryMatrixDualUniformCharacterSeries a =
      unitaryMatrixDualUniformCharacterSeries b) :
    a = b := by
  funext q
  rw [← unitaryMatrixDualL2CharacterAnalysis_uniformCharacterSeries a ha q,
    ← unitaryMatrixDualL2CharacterAnalysis_uniformCharacterSeries b hb q, heq]

end

end Mathematics
end YangMills
