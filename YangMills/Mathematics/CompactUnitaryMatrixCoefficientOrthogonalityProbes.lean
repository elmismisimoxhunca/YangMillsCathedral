/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryMatrixCoefficientOrthogonality

/-!
# Hostile probes for compact unitary matrix-coefficient orthogonality
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryMatrixCoefficientOrthogonality
namespace Probes

noncomputable section

universe uG

/-- Every index and the exact inverse-dimension coefficient survives in the self formula. -/
theorem exact_self_orthogonality
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n)
    (firstRow secondRow firstColumn secondColumn : Fin n) :
    (∫ g, star (ρ g firstRow firstColumn) *
        ρ g secondRow secondColumn ∂normalizedCompactHaarMeasure G) =
      (n : ℂ)⁻¹ * (if firstRow = secondRow then 1 else 0) *
        (if firstColumn = secondColumn then 1 else 0) :=
  normalizedCompactHaar_matrixCoefficient_orthogonality_self
    ρ hρ unitaryρ dimension_pos
    firstRow secondRow firstColumn secondColumn

/-- Inequivalent irreducible coefficient families have exactly zero mixed pairing. -/
theorem exact_inequivalent_orthogonality
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))]
    (targetRow targetColumn : Fin m)
    (sourceRow sourceColumn : Fin n) :
    (∫ g, star (σ g targetRow targetColumn) *
        ρ g sourceRow sourceColumn ∂normalizedCompactHaarMeasure G) = 0 :=
  normalizedCompactHaar_matrixCoefficient_orthogonality_inequivalent
    σ ρ hσ hρ unitaryσ targetRow targetColumn sourceRow sourceColumn

/-- Hostile probe: dropping the inverse-dimension factor on a matching coefficient forces
`n⁻¹ = 1`. -/
theorem missing_dimension_factor_requires_inverse_eq_one
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (row column : Fin n)
    (wrongNormalization :
      (∫ g, star (ρ g row column) * ρ g row column
        ∂normalizedCompactHaarMeasure G) = 1) :
    (n : ℂ)⁻¹ = 1 := by
  have exact := normalizedCompactHaar_matrixCoefficient_orthogonality_self
    ρ hρ unitaryρ dimension_pos row row column column
  simp only [if_pos] at exact
  simpa using exact.symm.trans wrongNormalization

end

end Probes
end CompactUnitaryMatrixCoefficientOrthogonality
end Mathematics
end YangMills
