/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatCharacterGenerator

/-!
# Hostile probes for the Casimir heat character generator
-/

namespace YangMills.Mathematics

open Filter
open scoped Topology

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))

/-- Exact diagonal action on a selected irreducible character. -/
theorem exact_casimirHeatOperator_character
    (t : ℝ) (ht : 0 < t) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (unitaryMatrixDualContinuousCharacter q) =
      (Real.exp (-(t / 2) * data.casimirWeight q) : ℂ) •
        unitaryMatrixDualContinuousCharacter q :=
  unitaryMatrixDualCasimirHeatComplexOperator_character data t ht q

/-- Exact coefficientwise heat action on an arbitrary finite selected-character combination. -/
theorem exact_casimirHeatOperator_finiteCharacterCombination
    (t : ℝ) (ht : 0 < t) (s : Finset (UnitaryMatrixDual G))
    (a : UnitaryMatrixDual G → ℂ) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (unitaryMatrixDualFiniteCharacterCombination s a) =
      unitaryMatrixDualCasimirHeatFiniteCharacterEvolution data t s a :=
  unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination data t ht s a

/-- Exact uniform-norm zero-time generator on every finite selected-character combination. -/
theorem exact_casimirHeatOperator_finiteCharacterCombination_generator
    (s : Finset (UnitaryMatrixDual G)) (a : UnitaryMatrixDual G → ℂ) :
    Tendsto
      (fun t : NNReal => ((t : ℂ)⁻¹) •
        (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
            (unitaryMatrixDualFiniteCharacterCombination s a) -
          unitaryMatrixDualFiniteCharacterCombination s a))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ q ∈ s,
        (((-(data.casimirWeight q / 2) : ℝ) : ℂ) * a q) •
          unitaryMatrixDualContinuousCharacter q)) :=
  tendsto_unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination_generator
    data s a

/-- Hostile finite-evolution probe: changing any resulting continuous function contradicts exact
coefficientwise heat action. -/
theorem changed_casimirHeatOperator_finiteCharacterEvolution_blocked
    (t : ℝ) (ht : 0 < t) (s : Finset (UnitaryMatrixDual G))
    (a : UnitaryMatrixDual G → ℂ) (changed : C(G, ℂ))
    (changed_ne_exact : changed ≠ unitaryMatrixDualCasimirHeatFiniteCharacterEvolution data t s a)
    (claimed : unitaryMatrixDualCasimirHeatComplexOperator data t
      (unitaryMatrixDualFiniteCharacterCombination s a) = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination data t ht s a))

/-- Hostile finite-generator probe: the uniform operator quotient cannot converge to an a.e. or
pointwise substitute with a different continuous-function target. -/
theorem changed_casimirHeatOperator_finiteCharacterGenerator_blocked
    (s : Finset (UnitaryMatrixDual G)) (a : UnitaryMatrixDual G → ℂ)
    (changed : C(G, ℂ))
    (changed_ne_exact : changed ≠ ∑ q ∈ s,
      (((-(data.casimirWeight q / 2) : ℝ) : ℂ) * a q) •
        unitaryMatrixDualContinuousCharacter q)
    (claimed : Tendsto
      (fun t : NNReal => ((t : ℂ)⁻¹) •
        (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
            (unitaryMatrixDualFiniteCharacterCombination s a) -
          unitaryMatrixDualFiniteCharacterCombination s a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination_generator
      data s a))

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- Exact scalar zero-time generator on every selected character eigenvalue. -/
theorem exact_casimirHeatEigenvalue_generator (q : UnitaryMatrixDual G) :
    Tendsto
      (fun t : NNReal =>
        (Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(data.casimirWeight q / 2))) :=
  tendsto_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero data q

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- Hostile probe: the scalar character generator cannot converge to a changed Casimir value. -/
theorem changed_casimirHeatEigenvalue_generator_blocked
    (q : UnitaryMatrixDual G) (changed : ℝ)
    (changed_ne_exact : changed ≠ -(data.casimirWeight q / 2))
    (claimed : Tendsto
      (fun t : NNReal =>
        (Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero data q))

end

end YangMills.Mathematics
