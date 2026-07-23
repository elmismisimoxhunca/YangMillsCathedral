/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupConjugationCentralization

/-!
# Hostile probes for conjugation-Haar centralization
-/

namespace YangMills
namespace Mathematics
namespace CompactGroupConjugationCentralization
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- The constructed map has exactly Hall's conjugation-average integrand and normalized Haar
measure. -/
theorem exact_centralization_formula (f : C(G, ℂ)) (x : G) :
    ((compactGroupConjugationCentralization (G := G) f :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) x =
      ∫ h, f (h * x * h⁻¹) ∂normalizedCompactHaarMeasure G :=
  compactGroupConjugationCentralization_apply f x

/-- Hostile convention probe: changing the integrand or conjugation order is contradictory. -/
theorem changed_centralization_formula_blocked
    (f : C(G, ℂ)) (x : G)
    (changed : ((compactGroupConjugationCentralization (G := G) f :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) x ≠
      ∫ h, f (h * x * h⁻¹) ∂normalizedCompactHaarMeasure G) : False :=
  changed (compactGroupConjugationCentralization_apply f x)

/-- The output satisfies the exact common-conjugator equation. -/
theorem exact_centralization_centrality (f : C(G, ℂ)) (x k : G) :
    ((compactGroupConjugationCentralization (G := G) f :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) (k * x * k⁻¹) =
    ((compactGroupConjugationCentralization (G := G) f :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) x :=
  (compactGroupConjugationCentralization f).property x k

/-- Every exact central function is fixed, with no scalar normalization ambiguity. -/
theorem exact_centralization_fixes
    (f : continuousCentralFunctionStarSubalgebra G) :
    compactGroupConjugationCentralization (f : C(G, ℂ)) = f :=
  compactGroupConjugationCentralization_fixes_central f

/-- The actual centralization map is surjective. -/
theorem exact_centralization_surjective :
    Function.Surjective (compactGroupConjugationCentralization (G := G)) :=
  compactGroupConjugationCentralization_surjective

/-- The averaging operator is norm-nonincreasing. -/
theorem exact_centralization_norm_bound (f : C(G, ℂ)) :
    ‖compactGroupConjugationCentralization (G := G) f‖ ≤ ‖f‖ :=
  compactGroupConjugationCentralizationLinear_norm f

/-- The whole continuous linear operator has norm at most one. -/
theorem exact_centralization_operator_norm :
    ‖compactGroupConjugationCentralization (G := G)‖ ≤ 1 :=
  compactGroupConjugationCentralization_norm_le_one

/-- Reapplying centralization after inclusion is exactly idempotent. -/
theorem exact_centralization_idempotent (f : C(G, ℂ)) :
    compactGroupConjugationCentralization
      ((compactGroupConjugationCentralization f :
        continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) =
      compactGroupConjugationCentralization f :=
  compactGroupConjugationCentralization_idempotent f

/-- Hostile noncollapse probe: the constructed operator cannot be zero. -/
theorem zero_constructed_centralization_blocked
    (collapsed : compactGroupConjugationCentralization (G := G) = 0) : False := by
  have hone := compactGroupConjugationCentralization_fixes_central
    (1 : continuousCentralFunctionStarSubalgebra G)
  rw [collapsed] at hone
  exact one_ne_zero hone.symm

/-- Once the one remaining Schur-to-character formula is supplied, it produces the exact abstract
bridge datum without additional hidden hypotheses. -/
theorem exact_remaining_formula_constructor
    (mapsCoefficientSynthesis : ∀ A : UnitaryMatrixDualCoefficientSpace G,
      ∃ c : UnitaryMatrixDualCharacterCoefficients G,
        compactGroupConjugationCentralization
          (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
            unitaryMatrixDualCentralCharacterSynthesis G c) :
    Nonempty (CompactGroupCharacterCentralizationData G) :=
  ⟨compactGroupCharacterCentralizationDataOfMapsCoefficientSynthesis mapsCoefficientSynthesis⟩

/-- The constructor preserves the supplied coefficient-to-character formula exactly. -/
theorem exact_remaining_formula_preserved
    (mapsCoefficientSynthesis : ∀ A : UnitaryMatrixDualCoefficientSpace G,
      ∃ c : UnitaryMatrixDualCharacterCoefficients G,
        compactGroupConjugationCentralization
          (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
            unitaryMatrixDualCentralCharacterSynthesis G c)
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      (compactGroupCharacterCentralizationDataOfMapsCoefficientSynthesis
        mapsCoefficientSynthesis).centralization
          (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
        unitaryMatrixDualCentralCharacterSynthesis G c :=
  mapsCoefficientSynthesis A

end

end Probes
end CompactGroupConjugationCentralization
end Mathematics
end YangMills
