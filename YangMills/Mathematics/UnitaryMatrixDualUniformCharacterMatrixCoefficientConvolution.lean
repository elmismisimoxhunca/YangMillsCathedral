/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryMatrixCoefficientCharacterConvolution
import YangMills.Mathematics.UnitaryMatrixDualUniformCharacterConvolution

/-!
# Matrix coefficients against uniformly summable selected-character series

The exact finite matrix-coefficient/character convolution law extends through an unconditionally
uniform selected-character series using the existing bounded linear convolution operator. A matrix
coefficient in an explicit irreducible presentation extracts the coefficient of its quotient class,
while retaining its original row, column, and basis.

No equivalence of raw coefficients, Peter--Weyl completeness, heat-kernel positivity, or generator
closure is asserted.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Continuous-map form of the selected character convolution law for one explicit matrix
coefficient. -/
theorem normalizedCompactHaarContinuousConvolution_matrixCoefficient_continuousCharacter
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (q : UnitaryMatrixDual G) :
    normalizedCompactHaarContinuousConvolution
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column)
      (unitaryMatrixDualContinuousCharacter q) =
      if unitaryMatrixDualClass ρ = q then
        (ρ.dimension : ℂ)⁻¹ •
          continuousMatrixRepresentationCoefficient ρ.representation
            ρ.continuous_representation row column
      else 0 := by
  ext z
  by_cases matching : unitaryMatrixDualClass ρ = q
  · rw [if_pos matching, ContinuousMap.smul_apply]
    change normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (unitaryMatrixDualCharacter q) z =
      (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column
    rw [normalizedCompactHaar_matrixCoefficient_unitaryMatrixDualCharacter_convolution,
      if_pos matching]
  · rw [if_neg matching]
    change normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (unitaryMatrixDualCharacter q) z = 0
    rw [normalizedCompactHaar_matrixCoefficient_unitaryMatrixDualCharacter_convolution,
      if_neg matching]

/-- A matrix coefficient on the left extracts its matching coefficient from a weighted uniformly
summable selected-character series on the right. -/
theorem normalizedCompactHaarContinuousConvolution_matrixCoefficient_uniformCharacterSeries
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension)
    (b : UnitaryMatrixDual G → ℂ)
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column)
      (unitaryMatrixDualUniformCharacterSeries b) =
      (b (unitaryMatrixDualClass ρ) * (ρ.dimension : ℂ)⁻¹) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column := by
  change normalizedCompactHaarContinuousConvolutionLeft
    (continuousMatrixRepresentationCoefficient ρ.representation
      ρ.continuous_representation row column)
    (∑' q, b q • unitaryMatrixDualContinuousCharacter q) = _
  rw [(normalizedCompactHaarContinuousConvolutionLeft
    (continuousMatrixRepresentationCoefficient ρ.representation
      ρ.continuous_representation row column)).map_tsum
        (summable_unitaryMatrixDualContinuousCharacter_smul b hb)]
  rw [tsum_eq_single (unitaryMatrixDualClass ρ)]
  · rw [map_smul, normalizedCompactHaarContinuousConvolutionLeft_apply,
      normalizedCompactHaarContinuousConvolution_matrixCoefficient_continuousCharacter,
      if_pos rfl]
    module
  · intro q hq
    rw [map_smul, normalizedCompactHaarContinuousConvolutionLeft_apply,
      normalizedCompactHaarContinuousConvolution_matrixCoefficient_continuousCharacter,
      if_neg (Ne.symm hq)]
    simp

end

end Mathematics
end YangMills
