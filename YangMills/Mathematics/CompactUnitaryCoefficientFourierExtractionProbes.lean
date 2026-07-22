/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryCoefficientFourierExtraction

/-!
# Hostile probes for Fourier extraction of compact unitary coefficients
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryCoefficientFourierExtraction
namespace Probes

noncomputable section

universe uG

/-- The exact self-transform retains the inverse dimension and forced transposed matrix unit. -/
theorem exact_transposed_matrix_unit
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (row column : Fin n) :
    normalizedCompactMatrixFourierCoefficient G ρ (fun g => ρ g row column) =
      (n : ℂ)⁻¹ • Matrix.single column row (1 : ℂ) :=
  normalizedCompactMatrixFourierCoefficient_matrixCoefficient_self
    ρ hρ unitaryρ dimension_pos row column

/-- Hostile probe: for distinct indices, replacing the forced transposed matrix unit by the
untransposed one is contradictory. -/
theorem untransposed_matrix_unit_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (row column : Fin n) (distinct : row ≠ column)
    (wrongOrientation :
      normalizedCompactMatrixFourierCoefficient G ρ (fun g => ρ g row column) =
        (n : ℂ)⁻¹ • Matrix.single row column (1 : ℂ)) : False := by
  have exactTransform :=
    normalizedCompactMatrixFourierCoefficient_matrixCoefficient_self
      ρ hρ unitaryρ dimension_pos row column
  have matricesEqual := exactTransform.symm.trans wrongOrientation
  have entryEqual := congrFun (congrFun matricesEqual column) row
  have dimension_ne_zero : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt dimension_pos)
  simp [distinct, Ne.symm distinct, dimension_ne_zero] at entryEqual

/-- An explicitly inequivalent irreducible coefficient has exactly zero transform. -/
theorem exact_inequivalent_zero
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation σ) (matrixRepresentation ρ))]
    (row column : Fin m) :
    normalizedCompactMatrixFourierCoefficient G ρ (fun g => σ g row column) = 0 :=
  normalizedCompactMatrixFourierCoefficient_matrixCoefficient_inequivalent
    σ ρ hσ hρ unitaryρ row column

end

end Probes
end CompactUnitaryCoefficientFourierExtraction
end Mathematics
end YangMills
