/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualUniformCharacterMatrixCoefficientConvolution

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Exact continuous selected-character branching probe for one matrix coordinate. -/
theorem exact_continuousMatrixCoefficient_selectedCharacter_convolution
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
      else 0 :=
  normalizedCompactHaarContinuousConvolution_matrixCoefficient_continuousCharacter
    ρ row column q

/-- Exact extraction from a weighted uniformly summable selected-character series. -/
theorem exact_continuousMatrixCoefficient_uniformCharacterSeries_convolution
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (b : UnitaryMatrixDual G → ℂ)
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    normalizedCompactHaarContinuousConvolution
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column)
      (unitaryMatrixDualUniformCharacterSeries b) =
      (b (unitaryMatrixDualClass ρ) * (ρ.dimension : ℂ)⁻¹) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column :=
  normalizedCompactHaarContinuousConvolution_matrixCoefficient_uniformCharacterSeries
    ρ row column b hb

/-- Hostile extraction probe: changing the matching-series output is contradictory. -/
theorem changed_continuousMatrixCoefficient_uniformCharacterSeries_convolution_blocked
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (b : UnitaryMatrixDual G → ℂ)
    (hb : Summable (fun q => ‖b q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (changed : C(G, ℂ))
    (changed_ne_exact : changed ≠
      (b (unitaryMatrixDualClass ρ) * (ρ.dimension : ℂ)⁻¹) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column)
    (claimed : normalizedCompactHaarContinuousConvolution
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column)
      (unitaryMatrixDualUniformCharacterSeries b) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (normalizedCompactHaarContinuousConvolution_matrixCoefficient_uniformCharacterSeries
      ρ row column b hb))

end

end Mathematics
end YangMills
