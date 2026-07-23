/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatCharacterSeries

/-!
# Hostile probes for Casimir-weighted heat character series
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatCharacterSeries
namespace Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The exact real coefficient retains Lévy's dimension and `t/2` normalization. -/
theorem exact_heat_coefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatCoefficientReal data t q =
      (unitaryMatrixDualDimension q : ℝ) *
        Real.exp (-(t / 2) * data.casimirWeight q) :=
  rfl

/-- Hostile normalization probe: changing the exact heat coefficient is contradictory. -/
theorem changed_heat_coefficient_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) {changed : ℝ}
    (hchanged : changed ≠ (unitaryMatrixDualDimension q : ℝ) *
      Real.exp (-(t / 2) * data.casimirWeight q))
    (changedCoefficient : unitaryMatrixDualCasimirHeatCoefficientReal data t q = changed) : False := by
  apply hchanged
  rw [← changedCoefficient]
  rfl

/-- The Weierstrass weight is exactly the heat-trace summand. -/
theorem exact_heat_trace_weight
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualCasimirHeatCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) =
      (unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) :=
  norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data t q

/-- The stored heat-trace premise conditionally forces the selected dual to be countable. -/
theorem exact_conditional_dual_countability
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) :
    Countable (UnitaryMatrixDual G) :=
  countable_unitaryMatrixDual_of_heatTraceSummability data

/-- Coefficients obey the exact dimension-cleared time-addition law. -/
theorem exact_heat_coefficient_time_addition
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (s t : ℝ) (q : UnitaryMatrixDual G) :
    (unitaryMatrixDualDimension q : ℝ) *
        unitaryMatrixDualCasimirHeatCoefficientReal data (s + t) q =
      unitaryMatrixDualCasimirHeatCoefficientReal data s q *
        unitaryMatrixDualCasimirHeatCoefficientReal data t q :=
  unitaryMatrixDualCasimirHeatCoefficientReal_add data s t q

variable [CompactSpace G]

/-- The positive-time finite-subset character net converges globally uniformly. -/
theorem exact_heat_character_finset_net_convergence
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, unitaryMatrixDualCasimirHeatCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualCasimirHeatCharacterSeries data t)) :=
  tendsto_finsetSum_unitaryMatrixDualCasimirHeatCharacter data ht

/-- The spectral candidate has the exact pointwise unconditional character `tsum`. -/
theorem exact_heat_character_pointwise_series
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatCharacterSeries data t g =
      ∑' q, (unitaryMatrixDualCasimirHeatCoefficientReal data t q : ℂ) *
        unitaryMatrixDualCharacter q g :=
  unitaryMatrixDualCasimirHeatCharacterSeries_apply data ht g

/-- Identity evaluation is the exact dimension-square heat trace. -/
theorem exact_heat_character_identity_trace
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    unitaryMatrixDualCasimirHeatCharacterSeries data t (1 : G) =
      ∑' q, (((unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) : ℝ) : ℂ) :=
  unitaryMatrixDualCasimirHeatCharacterSeries_one data ht

/-- The heat trace controls the exact global uniform norm. -/
theorem exact_heat_character_uniform_bound
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    ‖unitaryMatrixDualCasimirHeatCharacterSeries data t‖ ≤
      ∑' q, (unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) :=
  norm_unitaryMatrixDualCasimirHeatCharacterSeries_le data ht

/-- Hostile heat-trace bound probe: strict violation is contradictory. -/
theorem heat_character_uniform_bound_violation_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t)
    (violated : (∑' q, (unitaryMatrixDualDimension q : ℝ) ^ 2 *
      Real.exp (-(t / 2) * data.casimirWeight q)) <
      ‖unitaryMatrixDualCasimirHeatCharacterSeries data t‖) : False :=
  (not_lt_of_ge (norm_unitaryMatrixDualCasimirHeatCharacterSeries_le data ht)) violated

/-- The positive-time series is central, but no pointwise positivity of the summed function or
heat-kernel status is inferred. -/
theorem exact_heat_character_centrality
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g k : G) :
    (unitaryMatrixDualCasimirHeatCentralCharacterSeries data t ht : C(G, ℂ))
        (k * g * k⁻¹) =
      (unitaryMatrixDualCasimirHeatCentralCharacterSeries data t ht : C(G, ℂ)) g :=
  (unitaryMatrixDualCasimirHeatCentralCharacterSeries data t ht).property g k

variable [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Haar analysis recovers the exact Casimir heat coefficient. -/
theorem exact_heat_character_analysis
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (q : UnitaryMatrixDual G) :
    (∫ g, star (unitaryMatrixDualCharacter q g) *
      unitaryMatrixDualCasimirHeatCharacterSeries data t g
      ∂normalizedCompactHaarMeasure G) =
      unitaryMatrixDualCasimirHeatCoefficient data t q :=
  normalizedCompactHaar_characterAnalysis_casimirHeatCharacterSeries data ht q

/-- Hostile analysis probe: changing one recovered spectral coefficient is contradictory. -/
theorem changed_heat_character_analysis_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (q : UnitaryMatrixDual G) {changed : ℂ}
    (hchanged : changed ≠ unitaryMatrixDualCasimirHeatCoefficient data t q)
    (changedAnalysis : (∫ g, star (unitaryMatrixDualCharacter q g) *
      unitaryMatrixDualCasimirHeatCharacterSeries data t g
      ∂normalizedCompactHaarMeasure G) = changed) : False := by
  apply hchanged
  rw [← changedAnalysis]
  exact normalizedCompactHaar_characterAnalysis_casimirHeatCharacterSeries data ht q

end

end Probes
end UnitaryMatrixDualCasimirHeatCharacterSeries
end Mathematics
end YangMills
