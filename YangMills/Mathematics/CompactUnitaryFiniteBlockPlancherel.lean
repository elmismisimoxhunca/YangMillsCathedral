/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCoefficientSubspace

/-!
# Algebraic Plancherel on one compact irreducible coefficient block

For coefficient synthesis `f_A(g)=∑ᵢⱼ Aᵢⱼρ(g)ᵢⱼ`, matrix-coefficient orthogonality gives the exact
finite-block pairing

`∫ conj(f_A(g)) f_B(g) dμ_H(g) = n⁻¹ ∑ᵢⱼ conj(Aᵢⱼ) Bᵢⱼ`.

Combining this with `f̂_A(ρ)=n⁻¹Aᵀ` yields the dimension-weighted Fourier-side identity

`⟨f_A,f_B⟩ = n ⟨f̂_A(ρ),f̂_B(ρ)⟩_{HS}`.

This is algebraic Plancherel for one finite irreducible coefficient block. It does not sum over all
irreducible representations or assert Peter–Weyl completeness in `L²`.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- The coordinate Hilbert–Schmidt pairing on finite complex matrices. -/
def matrixHilbertSchmidtPairing
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ row, ∑ column, star (A row column) * B row column

/-- Simultaneous transpose preserves the coordinate Hilbert–Schmidt pairing. -/
theorem matrixHilbertSchmidtPairing_transpose
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixHilbertSchmidtPairing A.transpose B.transpose =
      matrixHilbertSchmidtPairing A B := by
  unfold matrixHilbertSchmidtPairing
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- The exact conjugate-linear/linear scalar law for the Hilbert–Schmidt pairing. -/
theorem matrixHilbertSchmidtPairing_smul
    {n : ℕ} (c d : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixHilbertSchmidtPairing (c • A) (d • B) =
      star c * d * matrixHilbertSchmidtPairing A B := by
  unfold matrixHilbertSchmidtPairing
  simp only [Matrix.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp only [smul_eq_mul]
  change (starRingEnd ℂ) (c * A row column) * (d * B row column) =
    (starRingEnd ℂ) c * d *
      ((starRingEnd ℂ) (A row column) * B row column)
  rw [map_mul]
  ring

/-- A matrix unit has Hilbert–Schmidt norm squared one. -/
theorem matrixHilbertSchmidtPairing_single_one
    {n : ℕ} (row column : Fin n) :
    matrixHilbertSchmidtPairing
      (Matrix.single row column (1 : ℂ))
      (Matrix.single row column (1 : ℂ)) = 1 := by
  classical
  unfold matrixHilbertSchmidtPairing
  rw [Finset.sum_eq_single row]
  · rw [Finset.sum_eq_single column]
    · simp
    · intro otherColumn _ column_ne
      simp [Ne.symm column_ne]
    · simp
  · intro otherRow _ row_ne
    apply Finset.sum_eq_zero
    intro otherColumn _
    simp [Ne.symm row_ne]
  · simp

/-- Exact normalized-Haar pairing of two synthesized coefficient matrices in one irreducible
unitary block. -/
theorem normalizedCompactHaar_coefficientSynthesis_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (∫ g, star (matrixCoefficientSynthesis ρ A g) *
        matrixCoefficientSynthesis ρ B g
      ∂normalizedCompactHaarMeasure G) =
      (n : ℂ)⁻¹ * matrixHilbertSchmidtPairing A B := by
  classical
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have integrableTerm (row column : Fin n) :
      Integrable (fun g =>
        star (A row column * ρ g row column) *
          matrixCoefficientSynthesis ρ B g) μ := by
    have continuousTerm : Continuous (fun g =>
        star (A row column * ρ g row column) *
          matrixCoefficientSynthesis ρ B g) := by
      apply Continuous.mul
      · exact
          (Continuous.const_mul
            (hρ.matrix_elem row column) (A row column)).star
      · exact continuous_matrixCoefficientSynthesis ρ hρ B
    simpa only [integrableOn_univ] using
      continuousTerm.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ g, star (matrixCoefficientSynthesis ρ A g) *
        matrixCoefficientSynthesis ρ B g ∂μ) =
        ∫ g, ∑ row, ∑ column,
          star (A row column * ρ g row column) *
            matrixCoefficientSynthesis ρ B g ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [matrixCoefficientSynthesis_apply]
      change (starRingEnd ℂ)
          (∑ row, ∑ column, A row column * ρ g row column) * _ = _
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      rw [map_sum, Finset.sum_mul]
      simp only [starRingEnd_apply]
    _ = ∑ row, ∑ column,
        ∫ g, star (A row column * ρ g row column) *
          matrixCoefficientSynthesis ρ B g ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro row _
        rw [integral_finsetSum Finset.univ]
        intro column _
        exact integrableTerm row column
      · intro row _
        exact integrable_finsetSum _ fun column _ =>
          integrableTerm row column
    _ = ∑ row, ∑ column, star (A row column) *
        ((n : ℂ)⁻¹ * B row column) := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      have transformEntry := congrFun (congrFun
        (normalizedCompactMatrixFourierCoefficient_synthesis
          ρ hρ unitaryρ dimension_pos B) column) row
      have transformEntry' :
          (∫ g, matrixCoefficientSynthesis ρ B g *
              ρ (g⁻¹) column row ∂μ) =
            (n : ℂ)⁻¹ * B row column := by
        simpa using transformEntry
      have coefficientPairing :
          (∫ g, star (ρ g row column) *
              matrixCoefficientSynthesis ρ B g ∂μ) =
            (n : ℂ)⁻¹ * B row column := by
        calc
          (∫ g, star (ρ g row column) *
              matrixCoefficientSynthesis ρ B g ∂μ) =
              ∫ g, matrixCoefficientSynthesis ρ B g *
                ρ (g⁻¹) column row ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with g
            rw [unitaryMatrixRepresentation_inv_apply
              ρ unitaryρ g column row]
            ring
          _ = (n : ℂ)⁻¹ * B row column := transformEntry'
      have factorIntegrand :
          (fun g => star (A row column * ρ g row column) *
              matrixCoefficientSynthesis ρ B g) =
            fun g => star (A row column) *
              (star (ρ g row column) *
                matrixCoefficientSynthesis ρ B g) := by
        funext g
        change (starRingEnd ℂ) (A row column * ρ g row column) *
          matrixCoefficientSynthesis ρ B g =
            (starRingEnd ℂ) (A row column) *
              ((starRingEnd ℂ) (ρ g row column) *
                matrixCoefficientSynthesis ρ B g)
        rw [map_mul]
        ring
      rw [factorIntegrand, integral_const_mul, coefficientPairing]
    _ = (n : ℂ)⁻¹ * matrixHilbertSchmidtPairing A B := by
      unfold matrixHilbertSchmidtPairing
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring

/-- Dimension-weighted Fourier Plancherel identity on one finite irreducible coefficient block. -/
theorem normalizedCompactHaar_coefficientSynthesis_fourier_plancherel
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (∫ g, star (matrixCoefficientSynthesis ρ A g) *
        matrixCoefficientSynthesis ρ B g
      ∂normalizedCompactHaarMeasure G) =
      (n : ℂ) * matrixHilbertSchmidtPairing
        (normalizedCompactMatrixFourierCoefficient G ρ
          (matrixCoefficientSynthesis ρ A))
        (normalizedCompactMatrixFourierCoefficient G ρ
          (matrixCoefficientSynthesis ρ B)) := by
  rw [normalizedCompactHaar_coefficientSynthesis_pairing
      ρ hρ unitaryρ dimension_pos A B,
    normalizedCompactMatrixFourierCoefficient_synthesis
      ρ hρ unitaryρ dimension_pos A,
    normalizedCompactMatrixFourierCoefficient_synthesis
      ρ hρ unitaryρ dimension_pos B,
    matrixHilbertSchmidtPairing_smul,
    matrixHilbertSchmidtPairing_transpose]
  have dimension_ne_zero : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt dimension_pos)
  have star_inverse_dimension :
      star ((n : ℂ)⁻¹) = (n : ℂ)⁻¹ := by
    change (starRingEnd ℂ) ((n : ℂ)⁻¹) = (n : ℂ)⁻¹
    rw [map_inv₀]
    simp
  rw [star_inverse_dimension]
  field_simp

end

end Mathematics
end YangMills
