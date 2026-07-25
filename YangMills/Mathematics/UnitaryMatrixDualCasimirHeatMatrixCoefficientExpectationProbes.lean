/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatMatrixCoefficientExpectation

/-! Hostile probes for conditional Casimir matrix-coefficient expectations. -/

namespace YangMills.Mathematics.UnitaryMatrixDualCasimirHeatMatrixCoefficientExpectation.Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
  (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
  (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)

include data positivity in
/-- The exact expectation retains the unchanged presentation and identity matrix entry. -/
theorem exact_matrixCoefficient_expectation
    {t : ℝ} (ht : 0 < t) (row column : Fin ρ.dimension) :
    (∫ g, ρ.representation g row column
      ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) =
    (Real.exp (-(t / 2) * data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) *
      ρ.representation 1 row column :=
  integral_matrixCoefficient_casimirHeatProbabilityMeasure
    data positivity ht ρ row column

include data positivity in
/-- Every diagonal raw coefficient has the exact positive Casimir scalar expectation. -/
theorem exact_diagonal_matrixCoefficient_expectation
    {t : ℝ} (ht : 0 < t) (row : Fin ρ.dimension) :
    (∫ g, ρ.representation g row row
      ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) =
    (Real.exp (-(t / 2) * data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) := by
  rw [integral_matrixCoefficient_casimirHeatProbabilityMeasure_eq_ite
    data positivity ht ρ row row]
  simp

include data positivity in
/-- Every off-diagonal raw coefficient has zero expectation. -/
theorem exact_offDiagonal_matrixCoefficient_expectation
    {t : ℝ} (ht : 0 < t) {row column : Fin ρ.dimension}
    (hne : row ≠ column) :
    (∫ g, ρ.representation g row column
      ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) = 0 := by
  rw [integral_matrixCoefficient_casimirHeatProbabilityMeasure_eq_ite
    data positivity ht ρ row column]
  simp [hne]

include data positivity in
/-- Hostile expectation probe: changing the retained matrix entry is rejected. -/
theorem changed_matrixCoefficient_expectation_blocked
    {t : ℝ} (ht : 0 < t) (row column : Fin ρ.dimension) (changed : ℂ)
    (hne : changed ≠
      (Real.exp (-(t / 2) * data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) *
        ρ.representation 1 row column)
    (changedValue :
      (∫ g, ρ.representation g row column
        ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) = changed) : False :=
  hne (changedValue.symm.trans
    (integral_matrixCoefficient_casimirHeatProbabilityMeasure
      data positivity ht ρ row column))

end

end YangMills.Mathematics.UnitaryMatrixDualCasimirHeatMatrixCoefficientExpectation.Probes
