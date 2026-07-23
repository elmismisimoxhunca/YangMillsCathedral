/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import YangMills.Mathematics.UnitaryMatrixDualCharacterL2Analysis

/-!
# Bessel bounds for selected compact-group characters

The selected irreducible character vectors form an orthonormal family in normalized-Haar `L²`.
Consequently every `L²` vector has square-summable selected-character analysis coefficients, with
Bessel bounds for finite sums and the unconditional `tsum`. In particular, every individual vector
has at most countably many nonzero selected-character coefficients even though no global
countability of the selected dual is assumed.

For finitely supported character synthesis, the norm-square and the coefficient `tsum` satisfy exact
finite Parseval identities.

These results do not assert that the character family spans all `L²`, the project's central
surrogate, or even an AE-central carrier. No infinite synthesis or inversion theorem is used.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The entire selected family of normalized-Haar `L²` irreducible characters is orthonormal. -/
theorem orthonormal_unitaryMatrixDualL2CharacterVector :
    Orthonormal ℂ (unitaryMatrixDualL2CharacterVector (G := G)) := by
  classical
  rw [orthonormal_iff_ite]
  intro q r
  rw [unitaryMatrixDualL2CharacterVector, unitaryMatrixDualL2CharacterVector,
    unitaryMatrixDualL2CharacterSynthesis_inner]
  by_cases h : q = r
  · simp [h, unitaryMatrixDualCharacterCoefficientPairing]
  · simp [h, unitaryMatrixDualCharacterCoefficientPairing]

/-- Finite Bessel inequality for selected-character analysis. -/
theorem sum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le
    (f : NormalizedCompactHaarL2 G) (s : Finset (UnitaryMatrixDual G)) :
    ∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  simpa only [unitaryMatrixDualL2CharacterAnalysis, innerSL_apply_apply] using
    (orthonormal_unitaryMatrixDualL2CharacterVector (G := G)).sum_inner_products_le f (s := s)

/-- Unconditional Bessel inequality over the possibly non-countable selected dual. -/
theorem tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le
    (f : NormalizedCompactHaarL2 G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  simpa only [unitaryMatrixDualL2CharacterAnalysis, innerSL_apply_apply] using
    (orthonormal_unitaryMatrixDualL2CharacterVector (G := G)).tsum_inner_products_le f

/-- Every normalized-Haar `L²` vector has a summable family of squared selected-character
coefficients. -/
theorem summable_norm_unitaryMatrixDualL2CharacterAnalysis_sq
    (f : NormalizedCompactHaarL2 G) :
    Summable (fun q => ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2) := by
  simpa only [unitaryMatrixDualL2CharacterAnalysis, innerSL_apply_apply] using
    (orthonormal_unitaryMatrixDualL2CharacterVector (G := G)).inner_products_summable f

/-- Although the entire selected dual need not be countable, each individual `L²` vector has at most
countably many nonzero selected-character coefficients. -/
theorem countable_setOf_unitaryMatrixDualL2CharacterAnalysis_ne_zero
    (f : NormalizedCompactHaarL2 G) :
    Set.Countable {q | unitaryMatrixDualL2CharacterAnalysis q f ≠ 0} := by
  apply (summable_norm_unitaryMatrixDualL2CharacterAnalysis_sq f).countable_support.mono
  intro q hq
  change q ∈ Function.support (fun q => ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2)
  rw [Function.mem_support]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)

/-- Continuous central functions have square-summable exact normalized-Haar character integrals. -/
theorem summable_norm_normalizedCompactHaar_characterCoefficient_sq
    (f : continuousCentralFunctionStarSubalgebra G) :
    Summable (fun q : UnitaryMatrixDual G =>
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2) := by
  simpa only [unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral] using
    summable_norm_unitaryMatrixDualL2CharacterAnalysis_sq
      (normalizedCompactHaarCentralContinuousToL2 G f)

/-- The exact normalized-Haar character integrals of a continuous central function satisfy Bessel's
inequality. -/
theorem tsum_norm_normalizedCompactHaar_characterCoefficient_sq_le
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∑' q : UnitaryMatrixDual G,
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2 ≤
      ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 := by
  simpa only [unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral] using
    tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le
      (normalizedCompactHaarCentralContinuousToL2 G f)

/-- Every continuous central function has at most countably many nonzero exact normalized-Haar
character integrals, without global selected-dual countability. -/
theorem countable_setOf_normalizedCompactHaar_characterCoefficient_ne_zero
    (f : continuousCentralFunctionStarSubalgebra G) :
    Set.Countable {q : UnitaryMatrixDual G |
      (∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G) ≠ 0} := by
  simpa only [unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral] using
    countable_setOf_unitaryMatrixDualL2CharacterAnalysis_ne_zero
      (normalizedCompactHaarCentralContinuousToL2 G f)

/-- Exact finite Parseval norm-square identity for finitely supported character synthesis. -/
theorem norm_unitaryMatrixDualL2CharacterSynthesis_sq
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    ‖unitaryMatrixDualL2CharacterSynthesis G c‖ ^ 2 =
      c.sum (fun _ a => ‖a‖ ^ 2) := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    unitaryMatrixDualL2CharacterSynthesis_inner]
  classical
  unfold unitaryMatrixDualCharacterCoefficientPairing
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]

/-- Exact unconditional Parseval equality on the finite character-synthesis range. -/
theorem tsum_norm_unitaryMatrixDualL2CharacterAnalysis_synthesis_sq
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterSynthesis G c)‖ ^ 2 =
      ‖unitaryMatrixDualL2CharacterSynthesis G c‖ ^ 2 := by
  rw [norm_unitaryMatrixDualL2CharacterSynthesis_sq]
  simp only [unitaryMatrixDualL2CharacterAnalysis_synthesis]
  rw [tsum_eq_sum (s := c.support)]
  · rfl
  · intro q hq
    have hc : c q = 0 := by simpa [Finsupp.mem_support_iff] using hq
    rw [hc, norm_zero, zero_pow]
    norm_num

end

end Mathematics
end YangMills
