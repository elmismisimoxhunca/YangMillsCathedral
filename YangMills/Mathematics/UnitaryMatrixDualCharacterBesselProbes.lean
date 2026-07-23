/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterBessel

/-!
# Hostile probes for selected-character Bessel bounds
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterBessel
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The full selected family is genuinely orthonormal. -/
theorem exact_character_orthonormality :
    Orthonormal ℂ (unitaryMatrixDualL2CharacterVector (G := G)) :=
  orthonormal_unitaryMatrixDualL2CharacterVector

/-- Distinct selected classes have orthogonal character vectors. -/
theorem exact_distinct_character_orthogonality
    {q r : UnitaryMatrixDual G} (hqr : q ≠ r) :
    inner ℂ (unitaryMatrixDualL2CharacterVector q)
      (unitaryMatrixDualL2CharacterVector r) = 0 :=
  orthonormal_unitaryMatrixDualL2CharacterVector.inner_eq_zero hqr

/-- Every finite selected family satisfies the exact Bessel bound. -/
theorem exact_finite_Bessel_bound
    (f : NormalizedCompactHaarL2 G) (s : Finset (UnitaryMatrixDual G)) :
    ∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  sum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le f s

/-- Hostile bound probe: strict violation of finite Bessel is contradictory. -/
theorem finite_Bessel_violation_blocked
    (f : NormalizedCompactHaarL2 G) (s : Finset (UnitaryMatrixDual G))
    (violated : ‖f‖ ^ 2 <
      ∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2) : False :=
  (not_lt_of_ge (sum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le f s)) violated

/-- The unconditional coefficient-square sum satisfies Bessel. -/
theorem exact_unconditional_Bessel_bound
    (f : NormalizedCompactHaarL2 G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le f

/-- Hostile unconditional bound probe: strict violation of unconditional Bessel is contradictory. -/
theorem unconditional_Bessel_violation_blocked
    (f : NormalizedCompactHaarL2 G)
    (violated : ‖f‖ ^ 2 <
      ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2) : False :=
  (not_lt_of_ge (tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_le f)) violated

/-- The unconditional coefficient-square family is summable. -/
theorem exact_coefficient_square_summability
    (f : NormalizedCompactHaarL2 G) :
    Summable (fun q => ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2) :=
  summable_norm_unitaryMatrixDualL2CharacterAnalysis_sq f

/-- Each vector has only countably many nonzero selected-character coefficients, without requiring
the entire selected dual to be countable. -/
theorem exact_vectorwise_countable_support
    (f : NormalizedCompactHaarL2 G) :
    Set.Countable {q | unitaryMatrixDualL2CharacterAnalysis q f ≠ 0} :=
  countable_setOf_unitaryMatrixDualL2CharacterAnalysis_ne_zero f

/-- Exact normalized-Haar character integrals of continuous central functions are square summable. -/
theorem exact_continuousCentral_characterCoefficient_summability
    (f : continuousCentralFunctionStarSubalgebra G) :
    Summable (fun q : UnitaryMatrixDual G =>
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2) :=
  summable_norm_normalizedCompactHaar_characterCoefficient_sq f

/-- Exact normalized-Haar character integrals satisfy the source-facing Bessel bound. -/
theorem exact_continuousCentral_characterCoefficient_Bessel_bound
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∑' q : UnitaryMatrixDual G,
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2 ≤
      ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 :=
  tsum_norm_normalizedCompactHaar_characterCoefficient_sq_le f

/-- Hostile source-facing bound probe: strict violation of the exact integral Bessel bound is
contradictory. -/
theorem continuousCentral_characterCoefficient_Bessel_violation_blocked
    (f : continuousCentralFunctionStarSubalgebra G)
    (violated : ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 <
      ∑' q : UnitaryMatrixDual G,
        ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
          ∂normalizedCompactHaarMeasure G‖ ^ 2) : False :=
  (not_lt_of_ge (tsum_norm_normalizedCompactHaar_characterCoefficient_sq_le f)) violated

/-- Each continuous central function has at most countably many nonzero exact character integrals. -/
theorem exact_continuousCentral_characterCoefficient_countable_support
    (f : continuousCentralFunctionStarSubalgebra G) :
    Set.Countable {q : UnitaryMatrixDual G |
      (∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G) ≠ 0} :=
  countable_setOf_normalizedCompactHaar_characterCoefficient_ne_zero f

/-- Finite character synthesis satisfies the exact norm-square identity. -/
theorem exact_finite_synthesis_norm_sq
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    ‖unitaryMatrixDualL2CharacterSynthesis G c‖ ^ 2 =
      c.sum (fun _ a => ‖a‖ ^ 2) :=
  norm_unitaryMatrixDualL2CharacterSynthesis_sq c

/-- Hostile finite-Parseval probe: changing the exact synthesis norm square is contradictory. -/
theorem changed_finite_synthesis_norm_sq_blocked
    (c : UnitaryMatrixDualCharacterCoefficients G) {changed : ℝ}
    (hchanged : changed ≠ c.sum (fun _ a => ‖a‖ ^ 2))
    (changedNorm : ‖unitaryMatrixDualL2CharacterSynthesis G c‖ ^ 2 = changed) : False := by
  apply hchanged
  rw [← changedNorm]
  exact norm_unitaryMatrixDualL2CharacterSynthesis_sq c

/-- The unconditional coefficient-square sum is exact on the finite synthesis range. -/
theorem exact_finite_synthesis_Parseval_tsum
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterSynthesis G c)‖ ^ 2 =
      ‖unitaryMatrixDualL2CharacterSynthesis G c‖ ^ 2 :=
  tsum_norm_unitaryMatrixDualL2CharacterAnalysis_synthesis_sq c

end

end Probes
end UnitaryMatrixDualCharacterBessel
end Mathematics
end YangMills
