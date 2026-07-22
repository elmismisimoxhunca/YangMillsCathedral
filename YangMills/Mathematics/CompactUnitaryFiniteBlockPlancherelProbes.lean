/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteBlockPlancherel

/-!
# Hostile probes for finite-block compact Plancherel
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryFiniteBlockPlancherel
namespace Probes

open MeasureTheory

noncomputable section

universe uG

/-- The coefficient-side pairing retains the exact inverse representation dimension. -/
theorem exact_coefficient_pairing
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
      (n : ℂ)⁻¹ * matrixHilbertSchmidtPairing A B :=
  normalizedCompactHaar_coefficientSynthesis_pairing
    ρ hρ unitaryρ dimension_pos A B

/-- The Fourier-side identity retains the representation-dimension weight. -/
theorem exact_dimension_weighted_fourier_pairing
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
          (matrixCoefficientSynthesis ρ B)) :=
  normalizedCompactHaar_coefficientSynthesis_fourier_plancherel
    ρ hρ unitaryρ dimension_pos A B

/-- Hostile normalization probe: if the dimension weight is dropped even for one diagonal matrix
unit, the representation dimension is forced to equal one. -/
theorem missing_dimension_weight_forces_dimension_one
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n)
    (wrong :
      let index : Fin n := ⟨0, dimension_pos⟩
      let matrixUnit := Matrix.single index index (1 : ℂ)
      (∫ g, star (matrixCoefficientSynthesis ρ matrixUnit g) *
          matrixCoefficientSynthesis ρ matrixUnit g
        ∂normalizedCompactHaarMeasure G) =
        matrixHilbertSchmidtPairing
          (normalizedCompactMatrixFourierCoefficient G ρ
            (matrixCoefficientSynthesis ρ matrixUnit))
          (normalizedCompactMatrixFourierCoefficient G ρ
            (matrixCoefficientSynthesis ρ matrixUnit))) :
    (n : ℂ) = 1 := by
  let index : Fin n := ⟨0, dimension_pos⟩
  let matrixUnit := Matrix.single index index (1 : ℂ)
  dsimp only at wrong
  have exactIdentity :=
    normalizedCompactHaar_coefficientSynthesis_fourier_plancherel
      ρ hρ unitaryρ dimension_pos matrixUnit matrixUnit
  let fourierNormSq := matrixHilbertSchmidtPairing
    (normalizedCompactMatrixFourierCoefficient G ρ
      (matrixCoefficientSynthesis ρ matrixUnit))
    (normalizedCompactMatrixFourierCoefficient G ρ
      (matrixCoefficientSynthesis ρ matrixUnit))
  have weightedEqualsUnweighted :
      (n : ℂ) * fourierNormSq = fourierNormSq :=
    exactIdentity.symm.trans wrong
  have dimension_ne_zero : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt dimension_pos)
  have star_inverse_dimension :
      star ((n : ℂ)⁻¹) = (n : ℂ)⁻¹ := by
    change (starRingEnd ℂ) ((n : ℂ)⁻¹) = (n : ℂ)⁻¹
    rw [map_inv₀]
    simp
  have fourierNormSq_value :
      fourierNormSq = (n : ℂ)⁻¹ * (n : ℂ)⁻¹ := by
    dsimp [fourierNormSq]
    rw [normalizedCompactMatrixFourierCoefficient_synthesis
        ρ hρ unitaryρ dimension_pos matrixUnit,
      matrixHilbertSchmidtPairing_smul,
      matrixHilbertSchmidtPairing_transpose,
      matrixHilbertSchmidtPairing_single_one,
      star_inverse_dimension]
    ring
  have fourierNormSq_ne_zero : fourierNormSq ≠ 0 := by
    rw [fourierNormSq_value]
    exact mul_ne_zero
      (inv_ne_zero dimension_ne_zero)
      (inv_ne_zero dimension_ne_zero)
  apply mul_right_cancel₀ fourierNormSq_ne_zero
  simpa using weightedEqualsUnweighted

end

end Probes
end CompactUnitaryFiniteBlockPlancherel
end Mathematics
end YangMills
