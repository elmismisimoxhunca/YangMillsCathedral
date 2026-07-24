/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatMatrixCoefficientGenerator

namespace YangMills
namespace Mathematics

open Filter
open scoped Topology

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))

/-- Exact heat action on one explicit irreducible matrix coefficient. -/
theorem exact_casimirHeatOperator_matrixCoefficient
    (t : ℝ) (ht : 0 < t)
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column) =
      (Real.exp (-(t / 2) *
        data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column :=
  unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
    data t ht ρ row column

/-- Exact uniform-norm zero-time generator on one explicit irreducible matrix coefficient. -/
theorem exact_casimirHeatOperator_matrixCoefficient_generator
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    Tendsto
      (fun t : NNReal => ((t : ℂ)⁻¹) •
        (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
            (continuousMatrixRepresentationCoefficient ρ.representation
              ρ.continuous_representation row column) -
          continuousMatrixRepresentationCoefficient ρ.representation
            ρ.continuous_representation row column))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((-(data.casimirWeight (unitaryMatrixDualClass ρ) / 2) : ℝ) : ℂ) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column)) :=
  tendsto_unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient_generator
    data ρ row column

/-- Hostile heat-action probe: a changed continuous coordinate output is contradictory. -/
theorem changed_casimirHeatOperator_matrixCoefficient_blocked
    (t : ℝ) (ht : 0 < t)
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (changed : C(G, ℂ))
    (changed_ne_exact : changed ≠
      (Real.exp (-(t / 2) *
        data.casimirWeight (unitaryMatrixDualClass ρ)) : ℂ) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column)
    (claimed : unitaryMatrixDualCasimirHeatComplexOperator data t
      (continuousMatrixRepresentationCoefficient ρ.representation
        ρ.continuous_representation row column) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient
      data t ht ρ row column))

/-- Hostile generator probe: no changed continuous-function target shares this uniform-norm
right-hand limit. -/
theorem changed_casimirHeatOperator_matrixCoefficient_generator_blocked
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) (changed : C(G, ℂ))
    (changed_ne_exact : changed ≠
      (((-(data.casimirWeight (unitaryMatrixDualClass ρ) / 2) : ℝ) : ℂ) •
        continuousMatrixRepresentationCoefficient ρ.representation
          ρ.continuous_representation row column))
    (claimed : Tendsto
      (fun t : NNReal => ((t : ℂ)⁻¹) •
        (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
            (continuousMatrixRepresentationCoefficient ρ.representation
              ρ.continuous_representation row column) -
          continuousMatrixRepresentationCoefficient ρ.representation
            ρ.continuous_representation row column))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_unitaryMatrixDualCasimirHeatComplexOperator_matrixCoefficient_generator
      data ρ row column))

end

end Mathematics
end YangMills
