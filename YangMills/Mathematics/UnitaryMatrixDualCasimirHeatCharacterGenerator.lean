/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatCharacterSeries
import YangMills.Mathematics.UnitaryMatrixDualUniformCharacterConvolution
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Casimir heat operator and zero-time generator on selected characters

The uniformly summable spectral heat series acts diagonally on every selected irreducible character.
This gives an unconditional zero-time generator theorem on the algebraic character core. It does not
extend the generator to every smooth function or assume Peter–Weyl completeness.
-/

namespace YangMills.Mathematics

open Filter
open scoped Topology

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Complex spectral heat operator with the project's fixed convolution orientation. -/
noncomputable def unitaryMatrixDualCasimirHeatComplexOperator
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (f : C(G, ℂ)) : C(G, ℂ) :=
  normalizedCompactHaarContinuousConvolution f
    (unitaryMatrixDualCasimirHeatCharacterSeries data t)

/-- The spectral heat operator acts diagonally on each selected character at positive time. -/
theorem unitaryMatrixDualCasimirHeatComplexOperator_character
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (ht : 0 < t) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (unitaryMatrixDualContinuousCharacter q) =
      (Real.exp (-(t / 2) * data.casimirWeight q) : ℂ) •
        unitaryMatrixDualContinuousCharacter q := by
  unfold unitaryMatrixDualCasimirHeatComplexOperator
  rw [show unitaryMatrixDualCasimirHeatCharacterSeries data t =
      unitaryMatrixDualUniformCharacterSeries
        (unitaryMatrixDualCasimirHeatCoefficient data t) by rfl]
  rw [normalizedCompactHaarContinuousConvolution_continuousCharacter_uniformCharacterSeries
    q (unitaryMatrixDualCasimirHeatCoefficient data t)
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)]
  congr 1
  unfold unitaryMatrixDualCasimirHeatCoefficient unitaryMatrixDualCasimirHeatCoefficientReal
  have hdim : (unitaryMatrixDualDimension q : ℂ) ≠ 0 := by
    exact_mod_cast (unitaryMatrixDualRepresentative q).dimension_pos.ne'
  field_simp
  push_cast
  rfl

/-- Canonical finitely supported coefficient vector represented by a finite set and a total
coefficient function. Coefficients outside `s` are discarded. -/
noncomputable def unitaryMatrixDualFiniteCharacterCoefficients
    (s : Finset (UnitaryMatrixDual G)) (a : UnitaryMatrixDual G → ℂ) :
    UnitaryMatrixDualCharacterCoefficients G :=
  ∑ q ∈ s, Finsupp.single q (a q)

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- The set/function presentation recovers a canonical coefficient vector when the set is its exact
support. -/
@[simp]
theorem unitaryMatrixDualFiniteCharacterCoefficients_support
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    unitaryMatrixDualFiniteCharacterCoefficients c.support c = c := by
  classical
  unfold unitaryMatrixDualFiniteCharacterCoefficients
  exact Finsupp.sum_single c

/-- Finite algebraic selected-character combination. -/
noncomputable def unitaryMatrixDualFiniteCharacterCombination
    (s : Finset (UnitaryMatrixDual G)) (a : UnitaryMatrixDual G → ℂ) : C(G, ℂ) :=
  ∑ q ∈ s, a q • unitaryMatrixDualContinuousCharacter q

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- The set/function combination is exactly canonical finite-support character synthesis. -/
theorem unitaryMatrixDualFiniteCharacterCombination_eq_synthesis
    (s : Finset (UnitaryMatrixDual G)) (a : UnitaryMatrixDual G → ℂ) :
    unitaryMatrixDualFiniteCharacterCombination s a =
      unitaryMatrixDualContinuousCharacterSynthesis G
        (unitaryMatrixDualFiniteCharacterCoefficients s a) := by
  unfold unitaryMatrixDualFiniteCharacterCombination
    unitaryMatrixDualFiniteCharacterCoefficients
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ext g
  exact congrFun (unitaryMatrixDualCharacterSynthesis_single q (a q)).symm g

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- Canonical finite-support synthesis agrees with the set/function combination on exact support. -/
theorem unitaryMatrixDualContinuousCharacterSynthesis_eq_finiteCharacterCombination
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    unitaryMatrixDualContinuousCharacterSynthesis G c =
      unitaryMatrixDualFiniteCharacterCombination c.support c := by
  rw [unitaryMatrixDualFiniteCharacterCombination_eq_synthesis,
    unitaryMatrixDualFiniteCharacterCoefficients_support]

/-- Positive-time coefficientwise heat evolution of a finite selected-character combination. -/
noncomputable def unitaryMatrixDualCasimirHeatFiniteCharacterEvolution
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (s : Finset (UnitaryMatrixDual G))
    (a : UnitaryMatrixDual G → ℂ) : C(G, ℂ) :=
  ∑ q ∈ s, (a q * Real.exp (-(t / 2) * data.casimirWeight q)) •
    unitaryMatrixDualContinuousCharacter q

/-- Coefficientwise heat evolution on the canonical finitely supported coefficient carrier. -/
noncomputable def unitaryMatrixDualCasimirHeatCharacterCoefficientEvolution
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (c : UnitaryMatrixDualCharacterCoefficients G) : C(G, ℂ) :=
  unitaryMatrixDualCasimirHeatFiniteCharacterEvolution data t c.support c

/-- Casimir generator synthesis on the canonical finitely supported coefficient carrier. -/
noncomputable def unitaryMatrixDualCasimirFiniteCharacterGeneratorSynthesis
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (c : UnitaryMatrixDualCharacterCoefficients G) : C(G, ℂ) :=
  ∑ q ∈ c.support,
    (((-(data.casimirWeight q / 2) : ℝ) : ℂ) * c q) •
      unitaryMatrixDualContinuousCharacter q

/-- The spectral heat operator acts coefficientwise on every finite selected-character combination. -/
theorem unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (ht : 0 < t) (s : Finset (UnitaryMatrixDual G))
    (a : UnitaryMatrixDual G → ℂ) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (unitaryMatrixDualFiniteCharacterCombination s a) =
      unitaryMatrixDualCasimirHeatFiniteCharacterEvolution data t s a := by
  unfold unitaryMatrixDualCasimirHeatComplexOperator
    unitaryMatrixDualFiniteCharacterCombination
    unitaryMatrixDualCasimirHeatFiniteCharacterEvolution
  change normalizedCompactHaarContinuousConvolutionRight
    (unitaryMatrixDualCasimirHeatCharacterSeries data t)
    (∑ q ∈ s, a q • unitaryMatrixDualContinuousCharacter q) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [map_smul, normalizedCompactHaarContinuousConvolutionRight_apply]
  change a q • unitaryMatrixDualCasimirHeatComplexOperator data t
    (unitaryMatrixDualContinuousCharacter q) = _
  rw [unitaryMatrixDualCasimirHeatComplexOperator_character data t ht q]
  module

/-- Exact coefficientwise heat action on canonical finite-support character synthesis. -/
theorem unitaryMatrixDualCasimirHeatComplexOperator_characterSynthesis
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (ht : 0 < t) (c : UnitaryMatrixDualCharacterCoefficients G) :
    unitaryMatrixDualCasimirHeatComplexOperator data t
      (unitaryMatrixDualContinuousCharacterSynthesis G c) =
      unitaryMatrixDualCasimirHeatCharacterCoefficientEvolution data t c := by
  rw [unitaryMatrixDualContinuousCharacterSynthesis_eq_finiteCharacterCombination]
  exact unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination
    data t ht c.support c

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- The scalar Casimir heat eigenvalue has the exact right-hand zero-time generator
`-c_q/2`. -/
theorem tendsto_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (q : UnitaryMatrixDual G) :
    Tendsto
      (fun t : NNReal =>
        (Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(data.casimirWeight q / 2))) := by
  rw [show -(data.casimirWeight q / 2) = -(1 / 2 : ℝ) * data.casimirWeight q by ring]
  let eigenvalue : ℝ → ℝ := fun t => Real.exp (-(t / 2) * data.casimirWeight q)
  have innerDerivativeRaw :=
    (((hasDerivAt_id (0 : ℝ)).neg.div_const 2).mul_const (data.casimirWeight q))
  have innerDerivative :
      HasDerivAt (fun t : ℝ => -(t / 2) * data.casimirWeight q)
        (-(1 / 2 : ℝ) * data.casimirWeight q) 0 :=
    (innerDerivativeRaw.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
      intro t
      change -(t / 2) * data.casimirWeight q = (-t) / 2 * data.casimirWeight q
      ring))).congr_deriv (by ring)
  have derivative : HasDerivAt eigenvalue
      (-(1 / 2 : ℝ) * data.casimirWeight q) 0 := by
    simpa [eigenvalue] using innerDerivative.exp
  have slopeLimit : Tendsto (slope eigenvalue 0) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(1 / 2 : ℝ) * data.casimirWeight q)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp
      derivative.hasDerivWithinAt
  have coe_tendsto : Tendsto (fun t : NNReal => (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact_mod_cast ht
  have composed := slopeLimit.comp coe_tendsto
  apply composed.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_ne : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp only [Function.comp_apply, slope, eigenvalue]
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
  rw [show -(0 / 2) * data.casimirWeight q = 0 by ring, Real.exp_zero]
  change _ = (Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) * (t : ℝ)⁻¹
  rw [mul_comm]

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] in
/-- Complex coercion of the exact scalar character-generator limit. -/
theorem tendsto_complex_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (q : UnitaryMatrixDual G) :
    Tendsto
      (fun t : NNReal =>
        (((Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) / (t : ℝ) : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((-(data.casimirWeight q / 2) : ℝ) : ℂ)) := by
  have realLimit := tendsto_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero data q
  have complexLimit := Complex.continuous_ofReal.continuousAt.tendsto.comp realLimit
  change Tendsto
    (fun t : NNReal =>
      (((Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) / (t : ℝ) : ℝ) : ℂ))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds ((-(data.casimirWeight q / 2) : ℝ) : ℂ)) at complexLimit
  exact complexLimit

/-- Exact zero-time generator on every finite selected-character combination, in the uniform norm
of `C(G, ℂ)`. -/
theorem tendsto_unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination_generator
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (s : Finset (UnitaryMatrixDual G)) (a : UnitaryMatrixDual G → ℂ) :
    Tendsto
      (fun t : NNReal =>
        ((t : ℂ)⁻¹) •
          (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
              (unitaryMatrixDualFiniteCharacterCombination s a) -
            unitaryMatrixDualFiniteCharacterCombination s a))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ q ∈ s,
        (((-(data.casimirWeight q / 2) : ℝ) : ℂ) * a q) •
          unitaryMatrixDualContinuousCharacter q)) := by
  have termLimit : ∀ q ∈ s, Tendsto
      (fun t : NNReal =>
        (((((Real.exp (-((t : ℝ) / 2) * data.casimirWeight q) - 1) / (t : ℝ) : ℝ) : ℂ) *
          a q) • unitaryMatrixDualContinuousCharacter q))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((((-(data.casimirWeight q / 2) : ℝ) : ℂ) * a q) •
        unitaryMatrixDualContinuousCharacter q)) := by
    intro q hq
    exact ((tendsto_complex_unitaryMatrixDualCasimirHeatEigenvalue_slope_zero data q).mul_const
      (a q)).smul_const (unitaryMatrixDualContinuousCharacter q)
  have sumLimit := tendsto_finsetSum s termLimit
  apply sumLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  rw [unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination
    data (t : ℝ) ht_pos s a]
  unfold unitaryMatrixDualCasimirHeatFiniteCharacterEvolution
    unitaryMatrixDualFiniteCharacterCombination
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ext x
  simp only [ContinuousMap.coe_sub, ContinuousMap.coe_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp [ht_ne]

/-- Exact uniform-norm zero-time generator on canonical finite-support character synthesis. -/
theorem tendsto_unitaryMatrixDualCasimirHeatComplexOperator_characterSynthesis_generator
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (c : UnitaryMatrixDualCharacterCoefficients G) :
    Tendsto
      (fun t : NNReal => ((t : ℂ)⁻¹) •
        (unitaryMatrixDualCasimirHeatComplexOperator data (t : ℝ)
            (unitaryMatrixDualContinuousCharacterSynthesis G c) -
          unitaryMatrixDualContinuousCharacterSynthesis G c))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (unitaryMatrixDualCasimirFiniteCharacterGeneratorSynthesis data c)) := by
  rw [unitaryMatrixDualContinuousCharacterSynthesis_eq_finiteCharacterCombination]
  exact
    tendsto_unitaryMatrixDualCasimirHeatComplexOperator_finiteCharacterCombination_generator
      data c.support c

end

end YangMills.Mathematics
