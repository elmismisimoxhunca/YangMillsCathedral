/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteRepresentationContragredient

/-!
# Hostile probes for contragredient coefficient expansion
-/

namespace YangMills
namespace Mathematics
namespace FiniteRepresentationContragredient
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G]

/-- The contragredient coefficient uses inverse, transpose, and therefore swapped indices exactly. -/
theorem exact_contragredient_coefficient
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (g : G) (i j : Fin n) :
    matrixRepresentationContragredient ρ g i j = ρ (g⁻¹) j i :=
  matrixRepresentationContragredient_apply ρ g i j

/-- Hostile convention probe: changing the swapped inverse coefficient is contradictory. -/
theorem changed_contragredient_coefficient_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (g : G) (i j : Fin n)
    (changed : matrixRepresentationContragredient ρ g i j ≠ ρ (g⁻¹) j i) : False :=
  changed (matrixRepresentationContragredient_apply ρ g i j)

/-- The contragredient retains the original group multiplication order. -/
theorem exact_contragredient_multiplication
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g h : G) :
    matrixRepresentationContragredient ρ (g * h) =
      matrixRepresentationContragredient ρ g *
        matrixRepresentationContragredient ρ h := by
  rw [map_mul]

/-- Under exact coordinate unitarity, the contragredient coefficient is pointwise scalar star. -/
theorem exact_contragredient_unitary_star
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (g : G) (i j : Fin n) :
    matrixRepresentationContragredient ρ g i j = star (ρ g i j) :=
  matrixRepresentationContragredient_apply_eq_star ρ unitaryρ g i j

/-- Hostile star probe: a changed conjugation convention is contradictory. -/
theorem changed_contragredient_star_blocked
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (g : G) (i j : Fin n)
    (changed : matrixRepresentationContragredient ρ g i j ≠ star (ρ g i j)) : False :=
  changed (matrixRepresentationContragredient_apply_eq_star ρ unitaryρ g i j)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Continuity is derived, not required independently, for the contragredient. -/
theorem exact_contragredient_continuity
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Continuous (matrixRepresentationContragredient ρ) :=
  continuous_matrixRepresentationContragredient ρ hρ

/-- Every selected summand has strictly positive dimension. -/
theorem selected_decomposition_positive_dimension
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (index : Fin (compactRepresentationSelectedUnitaryDecomposition ρ hρ).count) :
    0 < (compactRepresentationSelectedUnitaryDecomposition ρ hρ).dimension index :=
  (compactRepresentationSelectedUnitaryDecomposition ρ hρ).dimension_pos index

/-- Every selected summand is continuous, unitary, and irreducible on the same representative. -/
theorem selected_decomposition_exact_representation_properties
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (index : Fin (compactRepresentationSelectedUnitaryDecomposition ρ hρ).count) :
    Continuous ((compactRepresentationSelectedUnitaryDecomposition ρ hρ).representation index) ∧
    (∀ g, star ((compactRepresentationSelectedUnitaryDecomposition ρ hρ).representation index g) *
      (compactRepresentationSelectedUnitaryDecomposition ρ hρ).representation index g = 1) ∧
    Representation.IsIrreducible (matrixRepresentation
      ((compactRepresentationSelectedUnitaryDecomposition ρ hρ).representation index)) :=
  ⟨(compactRepresentationSelectedUnitaryDecomposition ρ hρ).continuous_representation index,
    (compactRepresentationSelectedUnitaryDecomposition ρ hρ).unitary_representation index,
    (compactRepresentationSelectedUnitaryDecomposition ρ hρ).irreducible_representation index⟩

/-- Dimension zero remains supported by the selected finite decomposition infrastructure. -/
theorem zero_dimension_selected_decomposition_available
    (ρ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hρ₀ : Continuous ρ₀) :
    Nonempty (CompactRepresentationSelectedUnitaryDecomposition 0 ρ₀) :=
  ⟨compactRepresentationSelectedUnitaryDecomposition ρ₀ hρ₀⟩

/-- The production star-expansion theorem is available on the unchanged unitary coefficient. -/
theorem exact_star_expansion_available
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (g : G) (row column : Fin n) :
    star (ρ g row column) = ∑ index, ∑ summandRow, ∑ summandColumn,
      finiteRepresentationDecompositionOutputCoordinate (matrixRepresentationContragredient ρ)
        (compactRepresentationSelectedUnitaryDecomposition
          (matrixRepresentationContragredient ρ)
          (continuous_matrixRepresentationContragredient ρ hρ)).summands
        (compactRepresentationSelectedUnitaryDecomposition
          (matrixRepresentationContragredient ρ)
          (continuous_matrixRepresentationContragredient ρ hρ)).decomposition index row
        (restrictedGroupAlgebraSubmoduleLinearEquiv (matrixRepresentationContragredient ρ)
          ((compactRepresentationSelectedUnitaryDecomposition
            (matrixRepresentationContragredient ρ)
            (continuous_matrixRepresentationContragredient ρ hρ)).summands index)
          (((compactRepresentationSelectedUnitaryDecomposition
            (matrixRepresentationContragredient ρ)
            (continuous_matrixRepresentationContragredient ρ hρ)).equivalence index).symm
            (Pi.single summandRow 1))) *
      (compactRepresentationSelectedUnitaryDecomposition
        (matrixRepresentationContragredient ρ)
        (continuous_matrixRepresentationContragredient ρ hρ)).representation index g
        summandRow summandColumn *
      (compactRepresentationSelectedUnitaryDecomposition
        (matrixRepresentationContragredient ρ)
        (continuous_matrixRepresentationContragredient ρ hρ)).equivalence index
        ((restrictedGroupAlgebraSubmoduleLinearEquiv (matrixRepresentationContragredient ρ)
          ((compactRepresentationSelectedUnitaryDecomposition
            (matrixRepresentationContragredient ρ)
            (continuous_matrixRepresentationContragredient ρ hρ)).summands index)).symm
          (finiteRepresentationDecompositionInput (matrixRepresentationContragredient ρ)
            (compactRepresentationSelectedUnitaryDecomposition
              (matrixRepresentationContragredient ρ)
              (continuous_matrixRepresentationContragredient ρ hρ)).summands
            (compactRepresentationSelectedUnitaryDecomposition
              (matrixRepresentationContragredient ρ)
              (continuous_matrixRepresentationContragredient ρ hρ)).decomposition
            (Pi.single column 1) index)) summandColumn :=
  matrixCoefficient_star_finite_selectedUnitary_expansion ρ hρ unitaryρ g row column

end

end Probes
end FiniteRepresentationContragredient
end Mathematics
end YangMills
