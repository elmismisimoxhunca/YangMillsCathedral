/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacters

/-!
# Hostile probes for all-class algebraic character synthesis
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacters
namespace Probes

open MeasureTheory

noncomputable section

universe uG

/-- Every synthesized character combination is exactly central. -/
theorem exact_all_class_centrality
    {G : Type uG} [Group G] [TopologicalSpace G]
    (coefficients : UnitaryMatrixDualCharacterCoefficients G)
    (g h : G) :
    unitaryMatrixDualCharacterSynthesis G coefficients (h * g * h⁻¹) =
      unitaryMatrixDualCharacterSynthesis G coefficients g :=
  unitaryMatrixDualCharacterSynthesis_conj coefficients g h

/-- Analysis against any selected character recovers its exact coefficient. -/
theorem exact_all_class_character_analysis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCharacterCoefficients G)
    (q : UnitaryMatrixDual G) :
    (∫ g, star (unitaryMatrixDualCharacter q g) *
        unitaryMatrixDualCharacterSynthesis G coefficients g
      ∂normalizedCompactHaarMeasure G) = coefficients q :=
  normalizedCompactHaar_unitaryMatrixDualCharacter_analysis coefficients q

/-- The normalized-Haar pairing is exactly the finite-support coordinate pairing. -/
theorem exact_all_class_character_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (first second : UnitaryMatrixDualCharacterCoefficients G) :
    (∫ g, star (unitaryMatrixDualCharacterSynthesis G first g) *
        unitaryMatrixDualCharacterSynthesis G second g
      ∂normalizedCompactHaarMeasure G) =
      unitaryMatrixDualCharacterCoefficientPairing first second :=
  normalizedCompactHaar_unitaryMatrixDualCharacterSynthesis_pairing
    first second

/-- Hostile noncollapse probe: the zero central function has only the zero finitely supported
character expansion. -/
theorem zero_character_synthesis_forces_zero_coefficients
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCharacterCoefficients G)
    (collapsed : unitaryMatrixDualCharacterSynthesis G coefficients = 0) :
    coefficients = 0 := by
  apply unitaryMatrixDualCharacterSynthesis_injective
  simpa using collapsed

/-- Hostile analysis probe: changing one recovered character coefficient is contradictory. -/
theorem changed_character_analysis_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCharacterCoefficients G)
    (q : UnitaryMatrixDual G)
    (changed :
      (∫ g, star (unitaryMatrixDualCharacter q g) *
          unitaryMatrixDualCharacterSynthesis G coefficients g
        ∂normalizedCompactHaarMeasure G) ≠ coefficients q) : False :=
  changed
    (normalizedCompactHaar_unitaryMatrixDualCharacter_analysis coefficients q)

/-- Scope probe: algebraic character coefficients retain explicit finite support. -/
theorem finite_character_support_retained
    {G : Type uG} [Group G] [TopologicalSpace G]
    (coefficients : UnitaryMatrixDualCharacterCoefficients G) :
    ∃ support : Finset (UnitaryMatrixDual G),
      ∀ q, q ∉ support → coefficients q = 0 := by
  exact ⟨coefficients.support, fun _ outside =>
    Finsupp.notMem_support_iff.mp outside⟩

end

end Probes
end UnitaryMatrixDualCharacters
end Mathematics
end YangMills
