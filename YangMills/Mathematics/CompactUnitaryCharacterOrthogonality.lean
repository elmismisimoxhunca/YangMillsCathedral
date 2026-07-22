/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryMatrixCoefficientOrthogonality

/-!
# Haar orthonormality of compact irreducible unitary characters

Summing the previously proved all-index matrix-coefficient formulas over diagonal entries gives the
character statements used by Lévy's Peter–Weyl discussion:

* every positive-dimensional irreducible unitary character has normalized `L²` norm one;
* characters of explicitly inequivalent irreducible unitary representations have mixed pairing
  zero.

All finite sums are moved through the Haar integral using genuine integrability. This establishes
character orthonormality for the represented irreducibles, not completeness or density of the family
of all irreducible characters.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- A positive-dimensional irreducible unitary character has normalized Haar `L²` norm one. -/
theorem normalizedCompactHaar_character_normSq_integral
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    (∫ g, star (Matrix.trace (ρ g)) * Matrix.trace (ρ g)
      ∂normalizedCompactHaarMeasure G) = 1 := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have coefficientIntegrable (first second : Fin n) :
      Integrable (fun g => star (ρ g first first) * ρ g second second) μ := by
    have continuousCoefficient : Continuous
        (fun g => star (ρ g first first) * ρ g second second) := by
      fun_prop
    simpa only [integrableOn_univ] using
      continuousCoefficient.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ g, star (Matrix.trace (ρ g)) * Matrix.trace (ρ g) ∂μ) =
        ∫ g, ∑ first, ∑ second,
          star (ρ g first first) * ρ g second second ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [Matrix.trace]
      change (starRingEnd ℂ) (∑ first, ρ g first first) *
        (∑ second, ρ g second second) = _
      rw [map_sum, Finset.sum_mul]
      simp only [starRingEnd_apply]
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum]
    _ = ∑ first, ∑ second,
        ∫ g, star (ρ g first first) * ρ g second second ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro first _
        rw [integral_finsetSum Finset.univ]
        intro second _
        exact coefficientIntegrable first second
      · intro first _
        exact integrable_finsetSum _ fun second _ =>
          coefficientIntegrable first second
    _ = 1 := by
      classical
      calc
        (∑ first, ∑ second,
            ∫ g, star (ρ g first first) * ρ g second second ∂μ) =
            ∑ _first : Fin n, (n : ℂ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro first _
          rw [Finset.sum_eq_single first]
          · simpa using
              normalizedCompactHaar_matrixCoefficient_orthogonality_self
                ρ hρ unitaryρ dimension_pos first first first first
          · intro second _ second_ne
            have orthogonality :=
              normalizedCompactHaar_matrixCoefficient_orthogonality_self
                ρ hρ unitaryρ dimension_pos first second first second
            simpa [Ne.symm second_ne] using orthogonality
          · simp
        _ = (n : ℂ) * (n : ℂ)⁻¹ := by simp
        _ = 1 := by
          exact mul_inv_cancel₀
            (Nat.cast_ne_zero.mpr (Nat.ne_of_gt dimension_pos))

/-- Characters of explicitly inequivalent irreducible unitary representations have zero normalized
Haar pairing. -/
theorem normalizedCompactHaar_character_orthogonality_inequivalent
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
      (matrixRepresentation ρ) (matrixRepresentation σ))] :
    (∫ g, star (Matrix.trace (σ g)) * Matrix.trace (ρ g)
      ∂normalizedCompactHaarMeasure G) = 0 := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have coefficientIntegrable (target : Fin m) (source : Fin n) :
      Integrable (fun g => star (σ g target target) * ρ g source source) μ := by
    have continuousCoefficient : Continuous
        (fun g => star (σ g target target) * ρ g source source) := by
      fun_prop
    simpa only [integrableOn_univ] using
      continuousCoefficient.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ g, star (Matrix.trace (σ g)) * Matrix.trace (ρ g) ∂μ) =
        ∫ g, ∑ target, ∑ source,
          star (σ g target target) * ρ g source source ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [Matrix.trace, Matrix.trace]
      change (starRingEnd ℂ) (∑ target, σ g target target) *
        (∑ source, ρ g source source) = _
      rw [map_sum, Finset.sum_mul]
      simp only [starRingEnd_apply]
      apply Finset.sum_congr rfl
      intro target _
      rw [Finset.mul_sum]
    _ = ∑ target, ∑ source,
        ∫ g, star (σ g target target) * ρ g source source ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro target _
        rw [integral_finsetSum Finset.univ]
        intro source _
        exact coefficientIntegrable target source
      · intro target _
        exact integrable_finsetSum _ fun source _ =>
          coefficientIntegrable target source
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro target _
      apply Finset.sum_eq_zero
      intro source _
      exact normalizedCompactHaar_matrixCoefficient_orthogonality_inequivalent
        σ ρ hσ hρ unitaryσ target target source source

end

end Mathematics
end YangMills
