/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryMatrixCoefficientCharacterConvolution

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Exact self-character convolution probe with unchanged row and column. -/
theorem exact_matrixCoefficient_traceCharacter_convolution_self
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (fun x => Matrix.trace (ρ.representation x)) z =
      (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column :=
  normalizedCompactHaar_matrixCoefficient_traceCharacter_convolution_self
    ρ row column z

/-- Exact inequivalent-character annihilation probe. -/
theorem exact_matrixCoefficient_traceCharacter_convolution_inequivalent
    (ρ σ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    [IsEmpty (Representation.Equiv (matrixRepresentation ρ.representation)
      (matrixRepresentation σ.representation))]
    (row column : Fin ρ.dimension) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (fun x => Matrix.trace (σ.representation x)) z = 0 :=
  normalizedCompactHaar_matrixCoefficient_traceCharacter_convolution_inequivalent
    ρ σ row column z

/-- Exact quotient-selected branching probe without identifying raw coefficients across bases. -/
theorem exact_matrixCoefficient_selectedCharacter_convolution
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (q : UnitaryMatrixDual G) (z : G) :
    normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (unitaryMatrixDualCharacter q) z =
      if unitaryMatrixDualClass ρ = q then
        (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column
      else 0 :=
  normalizedCompactHaar_matrixCoefficient_unitaryMatrixDualCharacter_convolution
    ρ row column q z

/-- Hostile output probe: a changed selected-character convolution value is contradictory. -/
theorem changed_matrixCoefficient_selectedCharacter_convolution_blocked
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (q : UnitaryMatrixDual G) (z : G)
    (changed : ℂ)
    (changed_ne_exact : changed ≠
      if unitaryMatrixDualClass ρ = q then
        (ρ.dimension : ℂ)⁻¹ * ρ.representation z row column
      else 0)
    (claimed : normalizedCompactHaarComplexConvolution G
      (fun x => ρ.representation x row column)
      (unitaryMatrixDualCharacter q) z = changed) : False := by
  apply changed_ne_exact
  rw [← claimed]
  exact normalizedCompactHaar_matrixCoefficient_unitaryMatrixDualCharacter_convolution
    ρ row column q z

end

end Mathematics
end YangMills
