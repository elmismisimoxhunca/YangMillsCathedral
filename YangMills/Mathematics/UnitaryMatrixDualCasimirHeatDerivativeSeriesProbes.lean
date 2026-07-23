/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatDerivativeSeries

/-!
# Hostile probes for the candidate Casimir heat derivative series
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatDerivativeSeries
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The derivative coefficient retains the exact `-(c_q/2)` factor. -/
theorem exact_derivative_coefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q =
      -(data.casimirWeight q / 2) *
        unitaryMatrixDualCasimirHeatCoefficientReal data t q :=
  rfl

/-- The extra Casimir factor is controlled by the heat trace at half the time. -/
theorem exact_absorption_bound
    (t c : ℝ) (ht : 0 < t) :
    (c / 2) * Real.exp (-(t / 2) * c) ≤
      (2 / t) * Real.exp (-((t / 2) / 2) * c) :=
  casimir_mul_exp_neg_half_le t c ht

/-- Hostile analytic probe: a strict violation of the absorption estimate is contradictory. -/
theorem absorption_bound_violation_blocked
    (t c : ℝ) (ht : 0 < t)
    (violation : (2 / t) * Real.exp (-((t / 2) / 2) * c) <
      (c / 2) * Real.exp (-(t / 2) * c)) : False :=
  (not_lt_of_ge (casimir_mul_exp_neg_half_le t c ht)) violation

/-- The exact weighted norm includes one Casimir factor and two dimension factors. -/
theorem exact_derivative_weight
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) =
      (data.casimirWeight q / 2) *
        (unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) :=
  norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data t q

/-- Positive-time heat-trace data really imply weighted derivative-series summability. -/
theorem exact_derivative_summability
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun q => ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
      (unitaryMatrixDualDimension q : ℝ)) :=
  summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data ht

/-- Every individual coefficient has the exact derivative value. -/
theorem exact_individual_coefficient_derivative
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    HasDerivAt (fun s => unitaryMatrixDualCasimirHeatCoefficientReal data s q)
      (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q) t :=
  hasDerivAt_unitaryMatrixDualCasimirHeatCoefficientReal data t q

variable [CompactSpace G]

/-- Exact finite-subset convergence occurs in the global uniform norm. -/
theorem exact_derivative_finset_net
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t)) :=
  tendsto_finsetSum_unitaryMatrixDualCasimirHeatDerivativeCharacter data ht

/-- Exact pointwise unconditional derivative-candidate `tsum`. -/
theorem exact_derivative_series_apply
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t g =
      ∑' q, (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q : ℂ) *
        unitaryMatrixDualCharacter q g :=
  unitaryMatrixDualCasimirHeatDerivativeCharacterSeries_apply data ht g

/-- Hostile value probe: replacing the exact pointwise `tsum` is contradictory. -/
theorem changed_derivative_series_value_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) (changed : ℂ)
    (hchanged : changed ≠ ∑' q,
      (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q : ℂ) *
        unitaryMatrixDualCharacter q g)
    (changedValue : unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t g = changed) : False := by
  apply hchanged
  rw [← changedValue]
  exact unitaryMatrixDualCasimirHeatDerivativeCharacterSeries_apply data ht g

/-- The derivative-candidate series has its exact Weierstrass norm bound. -/
theorem exact_derivative_series_norm_bound
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    ‖unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t‖ ≤
      ∑' q, ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) :=
  norm_unitaryMatrixDualCasimirHeatDerivativeCharacterSeries_le data ht

end

end Probes
end UnitaryMatrixDualCasimirHeatDerivativeSeries
end Mathematics
end YangMills
