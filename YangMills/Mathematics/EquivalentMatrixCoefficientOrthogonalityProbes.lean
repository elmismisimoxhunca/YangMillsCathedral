/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.EquivalentMatrixCoefficientOrthogonality

/-!
# Hostile probes for coefficient orthogonality across equivalent presentations
-/

namespace YangMills
namespace Mathematics
namespace EquivalentMatrixCoefficientOrthogonality
namespace Probes

open MeasureTheory

noncomputable section

universe uG

/-- Exact equivalent-presentation probe: the mixed Haar pairing retains both conjugated coordinate
change factors. -/
theorem exact_equivalent_presentation_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ))
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < m)
    (targetRow targetColumn : Fin n)
    (sourceRow sourceColumn : Fin m) :
    (∫ g, star (σ g targetRow targetColumn) *
        ρ g sourceRow sourceColumn ∂normalizedCompactHaarMeasure G) =
      (m : ℂ)⁻¹ *
        star (representationEquivMatrix equivalence targetRow sourceRow) *
          star (representationEquivInverseMatrix equivalence
            sourceColumn targetColumn) :=
  normalizedCompactHaar_matrixCoefficient_orthogonality_equivalent
    ρ σ equivalence hρ unitaryρ dimension_pos
      targetRow targetColumn sourceRow sourceColumn

/-- Hostile factor probe: changing the exact equivalence-dependent right side is contradictory. -/
theorem changed_equivalent_presentation_pairing_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ))
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < m)
    (targetRow targetColumn : Fin n)
    (sourceRow sourceColumn : Fin m)
    (changed :
      (∫ g, star (σ g targetRow targetColumn) *
          ρ g sourceRow sourceColumn ∂normalizedCompactHaarMeasure G) ≠
        (m : ℂ)⁻¹ *
          star (representationEquivMatrix equivalence targetRow sourceRow) *
            star (representationEquivInverseMatrix equivalence
              sourceColumn targetColumn)) : False :=
  changed (normalizedCompactHaar_matrixCoefficient_orthogonality_equivalent
    ρ σ equivalence hρ unitaryρ dimension_pos
      targetRow targetColumn sourceRow sourceColumn)

/-- Coherence probe: specializing the supplied equivalence to the identity recovers the exact
Kronecker-delta self-orthogonality formula rather than a new normalization. -/
theorem identity_equivalence_recovers_self_orthogonality
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < m)
    (firstRow secondRow firstColumn secondColumn : Fin m) :
    (∫ g, star (ρ g firstRow firstColumn) *
        ρ g secondRow secondColumn ∂normalizedCompactHaarMeasure G) =
      (m : ℂ)⁻¹ * (if firstRow = secondRow then 1 else 0) *
        (if firstColumn = secondColumn then 1 else 0) := by
  rw [normalizedCompactHaar_matrixCoefficient_orthogonality_equivalent
    ρ ρ (Representation.Equiv.refl (matrixRepresentation ρ)) hρ unitaryρ
      dimension_pos firstRow firstColumn secondRow secondColumn]
  by_cases rows : firstRow = secondRow <;>
    by_cases columns : firstColumn = secondColumn <;>
      simp [representationEquivMatrix, representationEquivInverseMatrix,
        Representation.Equiv.refl, rows, columns]

end

end Probes
end EquivalentMatrixCoefficientOrthogonality
end Mathematics
end YangMills
