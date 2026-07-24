/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatCharacterGenerator
import YangMills.Mathematics.UnitaryMatrixDualUniformCharacterMatrixCoefficientConvolution

/-!
# Casimir heat action and generator on matrix coefficients

The uniformly summable central character heat series acts diagonally on every matrix coefficient of
an explicit continuous irreducible unitary presentation. The output retains the original coordinate
basis and has scalar `exp (-(t/2)c_[ρ])`. The exact scalar slope theorem then gives the uniform-norm
right-hand zero-time generator `-c_[ρ]/2` on each coefficient.

This is an algebraic coefficient-core result. It does not prove that every continuous presentation
is smooth, identify the pairing Laplacian on coefficients, establish graph density, or extend the
generator to all smooth tests.
-/

namespace YangMills
namespace Mathematics

open Filter
open scoped Topology

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The spectral Casimir heat operator acts diagonally on every explicit irreducible unitary matrix
coefficient while preserving its original row and column. -/
theorem unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (ht : 0 < t)
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column) =
      (Real.exp (-(t / 2) *
        data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column := by
  unfold unitaryMatrixDualCasimirHeatComplexOperator
  rw [show unitaryMatrixDualCasimirHeatCharacterSeries data t =
      unitaryMatrixDualUniformCharacterSeries
        (unitaryMatrixDualCasimirHeatCoefficient data t) by rfl]
  rw [normalizedCompactHaarContinuousConvolution_matrixCoefficient_uniformCharacterSeries
    ρ row column (unitaryMatrixDualCasimirHeatCoefficient data t)
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)]
  congr 1
  unfold unitaryMatrixDualCasimirHeatCoefficient
    unitaryMatrixDualCasimirHeatCoefficientReal
  have dimensionEquality :
      unitaryMatrixDualDimension (unitaryMatrixDualClass ρ) = ρ.dimension :=
    (ContinuousUnitaryIrreducibleMatrixRepresentation.dimension_eq_of_isEquivalent
      (unitaryMatrixDual_equivalent_representative ρ)).symm
  rw [dimensionEquality]
  have dimensionNonzero : (ρ.dimension : ℂ) ≠ 0 := by
    exact_mod_cast ρ.dimension_pos.ne'
  field_simp
  push_cast
  rfl

/-- Exact right-hand zero-time generator on each explicit irreducible matrix coefficient, in the
uniform norm of `C(G, ℂ)`. -/
theorem tendsto_unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient_generator
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    Tendsto
      (fun t : NNReal =>
        ((t : ℂ)⁻¹) •
          (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
              (continuousMatrixRepresentationCoefficient ρ.representation
                ρ.continuous_representation row column) -
            continuousMatrixRepresentationCoefficient ρ.representation
              ρ.continuous_representation row column))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((-(data.casimirWeight (unitaryMatrixDualClass ρ) / 2) : ℝ) : ℂ) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column)) := by
  let coefficient : C(G, ℂ) :=
    continuousMatrixRepresentationCoefficient ρ.representation
      ρ.continuous_representation row column
  have scalarLimit :=
    tendsto_complex_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero
      data (unitaryMatrixDualClass ρ)
  have coefficientLimit := scalarLimit.smul_const coefficient
  apply coefficientLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have positiveTime : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have nonzeroTime : (t : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt positiveTime
  rw [unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
    data (t : ℝ) positiveTime ρ row column]
  ext g
  simp only [coefficient, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    smul_eq_mul]
  push_cast
  field_simp [nonzeroTime]

end

end Mathematics
end YangMills
