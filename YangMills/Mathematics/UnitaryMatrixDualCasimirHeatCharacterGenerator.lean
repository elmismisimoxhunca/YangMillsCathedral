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

end

end YangMills.Mathematics
