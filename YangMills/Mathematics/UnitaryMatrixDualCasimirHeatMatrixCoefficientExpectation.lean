/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatInitialIdentity
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatMatrixCoefficientGenerator
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatPositiveSemigroup

/-!
# Matrix-coefficient expectations under the conditional Casimir density

The already proved diagonal convolution action determines the expectation of every raw matrix
coefficient under the positive Casimir spectral measure. Evaluating the convolution at the identity,
using inversion symmetry of the positive spectral density, gives

`∫ ρ(g)ᵢⱼ p_t(g) dg = exp (-(t/2)c_[ρ]) · ρ(1)ᵢⱼ`.

Hence the expectation is the same scalar on diagonal entries and zero off diagonal. The original
presentation, row, and column are retained. This theorem remains conditional on heat-trace
summability and strict positivity; it constructs neither input and does not assert a geometric heat
kernel.
-/

namespace YangMills.Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Exact raw matrix-coefficient expectation under the conditional positive Casimir spectral
measure, retaining the identity matrix entry of the original presentation. -/
theorem integral_matrixCoefficient_casimirHeatProbabilityMeasure
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {t : ℝ} (ht : 0 < t)
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    (∫ g, ρ.representation g row column
      ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) =
    (Real.exp (-(t / 2) * data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) *
      ρ.representation 1 row column := by
  let f := continuousMatrixRepresentationCoefficient ρ.representation
    ρ.continuous_representation row column
  have operatorAtOne := congrArg (fun F : C(G, ℂ) => F 1)
    (unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
      data t ht ρ row column)
  have series_inv (g : G) :
      unitaryMatrixDualCasimirHeatCharacterSeries data t g⁻¹ =
        unitaryMatrixDualCasimirHeatCharacterSeries data t g := by
    rw [unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal data positivity ht g⁻¹,
      unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal data positivity ht g,
      unitaryMatrixDualCasimirHeatDensityReal_inv data ht]
  have operatorIntegral :
      (∫ g, f g * unitaryMatrixDualCasimirHeatCharacterSeries data t g
        ∂normalizedCompactHaarMeasure G) =
      (Real.exp (-(t / 2) * data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) *
        f 1 := by
    simpa [unitaryMatrixDualCasimirHeatComplexOperator,
      normalizedCompactHaarContinuousConvolution_apply, series_inv] using operatorAtOne
  change (∫ g, f g ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) = _
  rw [integral_casimirHeatProbabilityMeasure_eq_integral_characterSeries
    data positivity ht f]
  exact operatorIntegral

/-- Coordinate form: diagonal expectations are the Casimir heat scalar and off-diagonal
expectations vanish. -/
theorem integral_matrixCoefficient_casimirHeatProbabilityMeasure_eq_ite
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {t : ℝ} (ht : 0 < t)
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    (∫ g, ρ.representation g row column
      ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) =
    if row = column then
      (Real.exp (-(t / 2) * data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ)
    else 0 := by
  rw [integral_matrixCoefficient_casimirHeatProbabilityMeasure
    data positivity ht ρ row column]
  simp [Matrix.one_apply]

end

end YangMills.Mathematics
