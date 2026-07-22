/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixFourierCoefficient
import YangMills.Mathematics.CompactUnitaryMatrixCoefficientOrthogonality

/-!
# Fourier extraction of compact irreducible unitary matrix coefficients

For the convention

`f̂(ρ) = ∫ g, f(g) ρ(g⁻¹) dμ_H(g)`,

the Fourier transform at an irreducible unitary representation of its `(a,b)` matrix coefficient is
exactly the transposed matrix unit

`n⁻¹ E_{b,a}`.

The transpose is forced by `ρ(g⁻¹)ᵢⱼ = conj(ρ(g)ⱼᵢ)`. At an explicitly inequivalent irreducible
unitary representation, the transform is zero. These are finite coefficient-extraction statements;
they do not assert Peter–Weyl density, Fourier inversion for arbitrary functions, or Plancherel
completeness.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- The normalized-Haar Fourier transform of an irreducible unitary matrix coefficient at its own
representation is the inverse-dimension-scaled transposed matrix unit. -/
theorem normalizedCompactMatrixFourierCoefficient_matrixCoefficient_self
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (row column : Fin n) :
    normalizedCompactMatrixFourierCoefficient G ρ (fun g => ρ g row column) =
      (n : ℂ)⁻¹ • Matrix.single column row (1 : ℂ) := by
  classical
  ext outputRow outputColumn
  rw [normalizedCompactMatrixFourierCoefficient_apply]
  have integralAsPairing :
      (∫ g, ρ g row column * ρ (g⁻¹) outputRow outputColumn
        ∂normalizedCompactHaarMeasure G) =
        ∫ g, star (ρ g outputColumn outputRow) * ρ g row column
          ∂normalizedCompactHaarMeasure G := by
    apply integral_congr_ae
    filter_upwards [] with g
    rw [unitaryMatrixRepresentation_inv_apply
      ρ unitaryρ g outputRow outputColumn]
    ring
  rw [integralAsPairing,
    normalizedCompactHaar_matrixCoefficient_orthogonality_self
      ρ hρ unitaryρ dimension_pos outputColumn row outputRow column]
  change _ = (n : ℂ)⁻¹ *
    (if column = outputRow ∧ row = outputColumn then 1 else 0)
  by_cases columnMatch : outputColumn = row
  · subst outputColumn
    by_cases rowMatch : outputRow = column
    · subst outputRow
      simp
    · simp [rowMatch, Ne.symm rowMatch]
  · by_cases rowMatch : outputRow = column
    · subst outputRow
      simp [columnMatch, Ne.symm columnMatch]
    · simp [columnMatch, rowMatch,
        Ne.symm columnMatch, Ne.symm rowMatch]

/-- The normalized-Haar Fourier transform of a matrix coefficient vanishes at an explicitly
inequivalent irreducible unitary representation. Only the transform representation needs the
inverse/conjugate-entry law in this orientation. -/
theorem normalizedCompactMatrixFourierCoefficient_matrixCoefficient_inequivalent
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
    normalizedCompactMatrixFourierCoefficient G ρ (fun g => σ g row column) = 0 := by
  ext outputRow outputColumn
  rw [normalizedCompactMatrixFourierCoefficient_apply]
  have integralAsPairing :
      (∫ g, σ g row column * ρ (g⁻¹) outputRow outputColumn
        ∂normalizedCompactHaarMeasure G) =
        ∫ g, star (ρ g outputColumn outputRow) * σ g row column
          ∂normalizedCompactHaarMeasure G := by
    apply integral_congr_ae
    filter_upwards [] with g
    rw [unitaryMatrixRepresentation_inv_apply
      ρ unitaryρ g outputRow outputColumn]
    ring
  rw [integralAsPairing,
    normalizedCompactHaar_matrixCoefficient_orthogonality_inequivalent
      ρ σ hρ hσ unitaryρ outputColumn outputRow row column,
    Matrix.zero_apply]

end

end Mathematics
end YangMills
