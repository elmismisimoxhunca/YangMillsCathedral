/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterL2Analysis

/-!
# Hostile probes for normalized-Haar L² character analysis
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterL2Analysis
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The actual `L²` pairing retains the exact finitely supported coefficient pairing. -/
theorem exact_L2_character_pairing
    (c d : UnitaryMatrixDualCharacterCoefficients G) :
    inner ℂ (unitaryMatrixDualL2CharacterSynthesis G c)
      (unitaryMatrixDualL2CharacterSynthesis G d) =
      unitaryMatrixDualCharacterCoefficientPairing c d :=
  unitaryMatrixDualL2CharacterSynthesis_inner c d

/-- Every selected character vector has exact norm one. -/
theorem exact_character_vector_norm (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualL2CharacterVector q‖ = 1 :=
  norm_unitaryMatrixDualL2CharacterVector q

/-- Every selected character analysis functional has exact operator norm one. -/
theorem exact_character_analysis_norm (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualL2CharacterAnalysis q‖ = 1 :=
  norm_unitaryMatrixDualL2CharacterAnalysis q

/-- Hostile normalization probe: a changed character-vector norm is contradictory. -/
theorem changed_character_vector_norm_blocked
    (q : UnitaryMatrixDual G) {changed : ℝ} (hchanged : changed ≠ 1)
    (changedNorm : ‖unitaryMatrixDualL2CharacterVector q‖ = changed) : False := by
  apply hchanged
  rw [← changedNorm]
  exact norm_unitaryMatrixDualL2CharacterVector q

/-- Analysis exactly recovers every synthesized coordinate. -/
theorem exact_analysis_synthesis
    (c : UnitaryMatrixDualCharacterCoefficients G) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterSynthesis G c) = c q :=
  unitaryMatrixDualL2CharacterAnalysis_synthesis c q

/-- Hostile coordinate probe: a changed synthesized analysis coordinate is contradictory. -/
theorem changed_analysis_coordinate_blocked
    (c : UnitaryMatrixDualCharacterCoefficients G) (q : UnitaryMatrixDual G)
    {changed : ℂ} (hchanged : changed ≠ c q)
    (changedAnalysis : unitaryMatrixDualL2CharacterAnalysis q
      (unitaryMatrixDualL2CharacterSynthesis G c) = changed) : False := by
  apply hchanged
  rw [← changedAnalysis]
  exact unitaryMatrixDualL2CharacterAnalysis_synthesis c q

omit [T2Space G] in
/-- Continuous-central analysis has the exact normalized-Haar integral convention. -/
theorem exact_continuousCentral_analysis_integral
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualL2CharacterAnalysis q
      (normalizedCompactHaarCentralContinuousToL2 G f) =
      ∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G :=
  unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral f q

omit [T2Space G] in
/-- Hostile integral-convention probe: changing the continuous-central character integral value is
contradictory. -/
theorem changed_continuousCentral_analysis_integral_blocked
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G)
    {changed : ℂ}
    (hchanged : changed ≠ ∫ g, star (unitaryMatrixDualCharacter q g) *
      (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G)
    (changedAnalysis : unitaryMatrixDualL2CharacterAnalysis q
      (normalizedCompactHaarCentralContinuousToL2 G f) = changed) : False := by
  apply hchanged
  rw [← changedAnalysis]
  exact unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral f q

end

end Probes
end UnitaryMatrixDualCharacterL2Analysis
end Mathematics
end YangMills
