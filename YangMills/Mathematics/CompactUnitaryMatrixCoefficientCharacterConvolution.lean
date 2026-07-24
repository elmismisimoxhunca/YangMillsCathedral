/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryCoefficientStarSubalgebra
import YangMills.Mathematics.UnitaryMatrixDualCharacterConvolution
import YangMills.Mathematics.UnitaryMatrixDualCharacterTransport

/-!
# Matrix-coefficient convolution with irreducible characters

For normalized-Haar convolution

`(f ⋆ g)(z) = ∫ f(x) g(x⁻¹z) dμ_H(x)`,

this file proves that convolving an irreducible unitary matrix coefficient on the left with an
irreducible trace character on the right extracts the matching representation and multiplies by its
inverse dimension. The proof expands the trace and uses matrix-coefficient orthogonality directly;
raw coefficients are never identified across equivalent coordinate presentations.

No Peter--Weyl completeness, infinite character series, heat kernel, or smoothness theorem is used.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- A matrix coefficient convolved with the trace character of the same irreducible unitary
representation is inverse-dimension times that unchanged coefficient. -/
theorem normalizedCompactHaar_matrixCoefficient_traceCharacter_convolution_self
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (fun x => Matrix.trace (ρ.representation x)) z =
      (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  letI : Representation.IsIrreducible (matrixRepresentation ρ.representation) :=
    ρ.irreducible_representation
  rw [normalizedCompactHaarComplexConvolution_apply]
  simp_rw [map_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [unitaryMatrixRepresentation_inv_eq_conjTranspose
    ρ.representation ρ.unitary_representation]
  simp only [Matrix.conjTranspose_apply, Finset.mul_sum]
  have integrableTerm (middle diagonal : Fin ρ.dimension) :
      Integrable (fun x : G =>
        ρ.representation x row column *
          (star (ρ.representation x middle diagonal) *
            ρ.representation z middle diagonal)) μ := by
    have coefficientContinuous : Continuous (fun x : G =>
        ρ.representation x row column) :=
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column).continuous
    have conjugateContinuous : Continuous (fun x : G =>
        star (ρ.representation x middle diagonal)) :=
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation middle diagonal).continuous.star
    have continuousTerm : Continuous (fun x : G =>
        ρ.representation x row column *
          (star (ρ.representation x middle diagonal) *
            ρ.representation z middle diagonal)) :=
      coefficientContinuous.mul (conjugateContinuous.mul continuous_const)
    simpa only [integrableOn_univ] using
      continuousTerm.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ x, ∑ diagonal, ∑ middle,
        ρ.representation x row column *
          (star (ρ.representation x middle diagonal) *
            ρ.representation z middle diagonal) ∂μ) =
      ∑ diagonal, ∑ middle,
        ∫ x, ρ.representation x row column *
          (star (ρ.representation x middle diagonal) *
            ρ.representation z middle diagonal) ∂μ := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro diagonal _
          rw [integral_finsetSum]
          intro middle _
          exact integrableTerm middle diagonal
        · intro diagonal _
          exact MeasureTheory.integrable_finsetSum _
            (fun middle _ => integrableTerm middle diagonal)
    _ = ∑ diagonal, ∑ middle,
        ρ.representation z middle diagonal *
          (((ρ.dimension : ℂ)⁻¹ * if middle = row then 1 else 0) *
            if diagonal = column then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro diagonal _
      apply Finset.sum_congr rfl
      intro middle _
      calc
        (∫ x, ρ.representation x row column *
            (star (ρ.representation x middle diagonal) *
              ρ.representation z middle diagonal) ∂μ) =
          ρ.representation z middle diagonal *
            (∫ x, star (ρ.representation x middle diagonal) *
              ρ.representation x row column ∂μ) := by
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards [] with x
                ring
        _ = _ := by
          rw [normalizedCompactHaar_matrixCoefficient_orthogonality_self
            ρ.representation ρ.continuous_representation
            ρ.unitary_representation ρ.dimension_pos]
    _ = (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column := by
      simp [mul_comm]

/-- A matrix coefficient convolved with the trace character of an inequivalent irreducible unitary
representation vanishes. -/
theorem normalizedCompactHaar_matrixCoefficient_traceCharacter_convolution_inequivalent
    (ρ σ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    [IsEmpty (Representation.Equiv (matrixRepresentation ρ.representation)
      (matrixRepresentation σ.representation))]
    (row column : Fin ρ.dimension) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (fun x => Matrix.trace (σ.representation x)) z = 0 := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  letI : Representation.IsIrreducible (matrixRepresentation ρ.representation) :=
    ρ.irreducible_representation
  letI : Representation.IsIrreducible (matrixRepresentation σ.representation) :=
    σ.irreducible_representation
  rw [normalizedCompactHaarComplexConvolution_apply]
  simp_rw [map_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [unitaryMatrixRepresentation_inv_eq_conjTranspose
    σ.representation σ.unitary_representation]
  simp only [Matrix.conjTranspose_apply, Finset.mul_sum]
  have integrableTerm (middle diagonal : Fin σ.dimension) :
      Integrable (fun x : G =>
        ρ.representation x row column *
          (star (σ.representation x middle diagonal) *
            σ.representation z middle diagonal)) μ := by
    have coefficientContinuous : Continuous (fun x : G =>
        ρ.representation x row column) :=
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column).continuous
    have conjugateContinuous : Continuous (fun x : G =>
        star (σ.representation x middle diagonal)) :=
      (continuousMatrixRepresentationCoefficient σ.representation
        σ.continuous_representation middle diagonal).continuous.star
    have continuousTerm : Continuous (fun x : G =>
        ρ.representation x row column *
          (star (σ.representation x middle diagonal) *
            σ.representation z middle diagonal)) :=
      coefficientContinuous.mul (conjugateContinuous.mul continuous_const)
    simpa only [integrableOn_univ] using
      continuousTerm.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ x, ∑ diagonal, ∑ middle,
        ρ.representation x row column *
          (star (σ.representation x middle diagonal) *
            σ.representation z middle diagonal) ∂μ) =
      ∑ diagonal, ∑ middle,
        ∫ x, ρ.representation x row column *
          (star (σ.representation x middle diagonal) *
            σ.representation z middle diagonal) ∂μ := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro diagonal _
          rw [integral_finsetSum]
          intro middle _
          exact integrableTerm middle diagonal
        · intro diagonal _
          exact MeasureTheory.integrable_finsetSum _
            (fun middle _ => integrableTerm middle diagonal)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro diagonal _
      apply Finset.sum_eq_zero
      intro middle _
      calc
        (∫ x, ρ.representation x row column *
            (star (σ.representation x middle diagonal) *
              σ.representation z middle diagonal) ∂μ) =
          σ.representation z middle diagonal *
            (∫ x, star (σ.representation x middle diagonal) *
              ρ.representation x row column ∂μ) := by
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards [] with x
                ring
        _ = 0 := by
          rw [normalizedCompactHaar_matrixCoefficient_orthogonality_inequivalent
            σ.representation ρ.representation σ.continuous_representation
            ρ.continuous_representation σ.unitary_representation]
          simp

/-- Unified selected-character convolution law for a coefficient in an arbitrary explicit
presentation. Equality is tested at the quotient class, but the output keeps the original raw
coordinate coefficient. -/
theorem normalizedCompactHaar_matrixCoefficient_unitaryMatrixDualCharacter_convolution
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (q : UnitaryMatrixDual G) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (unitaryMatrixDualCharacter q) z =
      if unitaryMatrixDualClass ρ = q then
        (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column
      else 0 := by
  by_cases matching : unitaryMatrixDualClass ρ = q
  · rw [if_pos matching]
    subst q
    rw [unitaryMatrixDualCharacter_class_eq_fun]
    exact normalizedCompactHaar_matrixCoefficient_traceCharacter_convolution_self
      ρ row column z
  · rw [if_neg matching]
    let σ := unitaryMatrixDualRepresentative q
    letI : IsEmpty (Representation.Equiv (matrixRepresentation ρ.representation)
        (matrixRepresentation σ.representation)) :=
      ⟨fun equivalence => by
        have classEquality : unitaryMatrixDualClass ρ = unitaryMatrixDualClass σ :=
          (unitaryMatrixDualClass_eq_iff ρ σ).mpr ⟨equivalence⟩
        exact matching (classEquality.trans (unitaryMatrixDualClass_representative q))⟩
    change normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (fun x => Matrix.trace (σ.representation x)) z = 0
    exact normalizedCompactHaar_matrixCoefficient_traceCharacter_convolution_inequivalent
      ρ σ row column z

end

end Mathematics
end YangMills
