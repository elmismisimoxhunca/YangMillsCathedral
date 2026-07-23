/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupConjugationCharacterFormula

/-!
# Hostile probes for the conjugation-average character formula
-/

namespace YangMills
namespace Mathematics
namespace CompactGroupConjugationCharacterFormula
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] in
/-- Coefficient synthesis uses the forced transpose in the trace formula. -/
theorem exact_coefficient_trace_transpose
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    matrixCoefficientSynthesis ρ A g = Matrix.trace (ρ g * A.transpose) :=
  matrixCoefficientSynthesis_eq_trace_mul_transpose ρ A g

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] in
/-- Hostile transpose probe: replacing `Aᵀ` in the trace formula is contradictory. -/
theorem changed_coefficient_trace_transpose_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (g : G)
    (changed : matrixCoefficientSynthesis ρ A g ≠
      Matrix.trace (ρ g * A.transpose)) : False :=
  changed (matrixCoefficientSynthesis_eq_trace_mul_transpose ρ A g)

/-- The conjugation average leaves exactly the existing normalized-Haar Schur average. -/
theorem exact_trace_of_schur_average
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (A : Matrix (Fin n) (Fin n) ℂ) (x : G) :
    compactGroupConjugationAverage (continuousMatrixCoefficientSynthesis ρ hρ A) x =
      Matrix.trace (ρ x * compactHaarIntertwinerAverage ρ ρ A.transpose) :=
  compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_trace_average ρ hρ A x

/-- The exact positive-dimensional irreducible weight is inverse dimension times trace. -/
theorem exact_inverse_dimension_character_weight
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) (x : G) :
    compactGroupConjugationAverage (continuousMatrixCoefficientSynthesis ρ hρ A) x =
      ((n : ℂ)⁻¹ * Matrix.trace A) * Matrix.trace (ρ x) :=
  compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_character ρ hρ hn A x

/-- Hostile normalization probe: changing the inverse-dimension character formula is contradictory. -/
theorem changed_inverse_dimension_character_weight_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) (x : G)
    (changed : compactGroupConjugationAverage
      (continuousMatrixCoefficientSynthesis ρ hρ A) x ≠
      ((n : ℂ)⁻¹ * Matrix.trace A) * Matrix.trace (ρ x)) : False :=
  changed (compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_character
    ρ hρ hn A x)

variable [SecondCountableTopology G]

/-- One selected coefficient block centralizes to the exact singleton character coefficient. -/
theorem exact_selected_single_character_image
    (q : UnitaryMatrixDual G)
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    compactGroupConjugationCentralization
      (unitaryMatrixDualContinuousCoefficientSynthesis G
        (unitaryMatrixDualCoefficientSingle q A)) =
    unitaryMatrixDualCentralCharacterSynthesis G
      (Finsupp.single q
        ((unitaryMatrixDualDimension q : ℂ)⁻¹ * Matrix.trace A)) :=
  compactGroupConjugationCentralization_coefficientSingle q A

/-- Every finite-support coefficient synthesis has a genuine finite-support character image. -/
theorem exact_all_finite_character_image
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      compactGroupConjugationCentralization
        (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
      unitaryMatrixDualCentralCharacterSynthesis G c :=
  compactGroupConjugationCentralization_maps_coefficientSynthesis A

/-- The constructed bridge datum uses the actual Haar centralization map. -/
theorem exact_constructed_bridge_centralization :
    (compactGroupCharacterCentralizationData G).centralization =
      compactGroupConjugationCentralization :=
  rfl

/-- Full continuous density now implies central uniform density under second countability. -/
theorem exact_full_to_central_density
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  density.hasCentralContinuousPeterWeylDensity_of_secondCountable

/-- Full continuous density now also implies the central normalized-Haar `L²` target. -/
theorem exact_full_to_central_L2_completeness
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  density.hasCentralL2PeterWeylCompleteness_of_secondCountable

/-- Faithful finite matrix coordinates now imply central uniform density. -/
theorem exact_faithful_central_density
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful

/-- Faithful finite matrix coordinates now imply the central normalized-Haar `L²` target. -/
theorem exact_faithful_central_L2_completeness
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful faithful

/-- Hostile endpoint probe: failed central density contradicts faithful matrix coordinates. -/
theorem failed_central_density_blocks_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (failed : ¬ UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G) : False :=
  failed (unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful)

end

end Probes
end CompactGroupConjugationCharacterFormula
end Mathematics
end YangMills
