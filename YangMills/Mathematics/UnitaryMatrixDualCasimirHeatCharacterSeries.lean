/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterUniformSeriesAnalysis

/-!
# Casimir-weighted character series with heat-trace summability

Lévy's compact-group heat-kernel expansion has coefficients

`dim(q) * exp (-(t/2) * c_q)`.

This file isolates the exact analytic premise needed to make that expression meaningful in the
current selected continuous unitary dual. `UnitaryMatrixDualHeatTraceSummabilityData` supplies a
nonnegative candidate Casimir weight `c_q` and requires the heat-trace family

`∑ q, dim(q)^2 exp (-(t/2) c_q)`

to be summable for every `t > 0`. From that premise this file constructs the unconditional,
globally uniformly convergent continuous-central character series and proves its pointwise formula,
identity heat-trace value, global norm bound, coefficient recovery, coefficient addition law, and
conditional countability of the selected dual.

No inhabitant of the summability data is constructed. In particular, this file does not identify the
weights with eigenvalues of Driver's geometric Laplacian, prove a heat equation or convolution
semigroup, prove pointwise positivity of the summed function or Haar normalization, or call the series a heat kernel. Those are
separate obligations.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Explicit candidate Casimir weights plus the positive-time heat-trace summability required for a
uniform character expansion. This is uninhabited data, not a Casimir theorem. -/
structure UnitaryMatrixDualHeatTraceSummabilityData where
  casimirWeight : UnitaryMatrixDual G → ℝ
  casimirWeight_nonneg : ∀ q, 0 ≤ casimirWeight q
  heatTrace_summable : ∀ (t : ℝ), 0 < t → Summable (fun q =>
    (unitaryMatrixDualDimension q : ℝ) ^ 2 *
      Real.exp (-(t / 2) * casimirWeight q))

/-- Real positive-time coefficient `dim(q) exp (-(t/2)c_q)`. -/
noncomputable def unitaryMatrixDualCasimirHeatCoefficientReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) : ℝ :=
  (unitaryMatrixDualDimension q : ℝ) *
    Real.exp (-(t / 2) * data.casimirWeight q)

/-- Complex coercion of the real Casimir heat coefficient. -/
noncomputable def unitaryMatrixDualCasimirHeatCoefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) : ℂ :=
  (unitaryMatrixDualCasimirHeatCoefficientReal data t q : ℂ)

/-- Every real Casimir heat coefficient is nonnegative. -/
theorem unitaryMatrixDualCasimirHeatCoefficientReal_nonneg
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    0 ≤ unitaryMatrixDualCasimirHeatCoefficientReal data t q := by
  unfold unitaryMatrixDualCasimirHeatCoefficientReal
  exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le

/-- The character Weierstrass weight is exactly the supplied heat-trace summand. -/
theorem norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualCasimirHeatCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) =
      (unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) := by
  rw [unitaryMatrixDualCasimirHeatCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (unitaryMatrixDualCasimirHeatCoefficientReal_nonneg data t q)]
  unfold unitaryMatrixDualCasimirHeatCoefficientReal
  ring

/-- Positive-time heat-trace summability supplies the exact weighted character-series premise. -/
theorem summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun q => ‖unitaryMatrixDualCasimirHeatCoefficient data t q‖ *
      (unitaryMatrixDualDimension q : ℝ)) := by
  simpa only [norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension] using
    data.heatTrace_summable t ht

/-- Heat-trace summability itself forces the selected dual to be countable, since every heat-trace
summand is strictly positive. This remains conditional on the uninhabited data. -/
theorem countable_unitaryMatrixDual_of_heatTraceSummability
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) :
    Countable (UnitaryMatrixDual G) := by
  apply Set.countable_univ_iff.mp
  have hc := (data.heatTrace_summable 1 zero_lt_one).countable_support
  apply hc.mono
  intro q hq
  change q ∈ Function.support (fun q =>
    (unitaryMatrixDualDimension q : ℝ) ^ 2 *
      Real.exp (-(1 / 2) * data.casimirWeight q))
  rw [Function.mem_support]
  apply mul_ne_zero
  · exact pow_ne_zero 2 (by
      exact_mod_cast (unitaryMatrixDualRepresentative q).dimension_pos.ne')
  · exact Real.exp_ne_zero _

/-- Exact multiplicative time-addition law after clearing one dimension factor. -/
theorem unitaryMatrixDualCasimirHeatCoefficientReal_add
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (s t : ℝ) (q : UnitaryMatrixDual G) :
    (unitaryMatrixDualDimension q : ℝ) *
        unitaryMatrixDualCasimirHeatCoefficientReal data (s + t) q =
      unitaryMatrixDualCasimirHeatCoefficientReal data s q *
        unitaryMatrixDualCasimirHeatCoefficientReal data t q := by
  unfold unitaryMatrixDualCasimirHeatCoefficientReal
  rw [show -((s + t) / 2) * data.casimirWeight q =
    -(s / 2) * data.casimirWeight q + -(t / 2) * data.casimirWeight q by ring]
  rw [Real.exp_add]
  ring

variable [CompactSpace G]

/-- The Casimir-weighted positive-time selected-character series in the global uniform norm. -/
noncomputable def unitaryMatrixDualCasimirHeatCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) : C(G, ℂ) :=
  unitaryMatrixDualUniformCharacterSeries
    (unitaryMatrixDualCasimirHeatCoefficient data t)

/-- Positive-time Casimir-weighted character series packaged as a continuous central function. -/
noncomputable def unitaryMatrixDualCasimirHeatCentralCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (ht : 0 < t) : continuousCentralFunctionStarSubalgebra G :=
  unitaryMatrixDualUniformCentralCharacterSeries
    (unitaryMatrixDualCasimirHeatCoefficient data t)
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)

/-- Exact unconditional finite-subset convergence in the global uniform norm. -/
theorem tendsto_finsetSum_unitaryMatrixDualCasimirHeatCharacter
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, unitaryMatrixDualCasimirHeatCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualCasimirHeatCharacterSeries data t)) :=
  tendsto_finsetSum_unitaryMatrixDualContinuousCharacter _
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)

/-- Exact pointwise Casimir-weighted character `tsum`. -/
theorem unitaryMatrixDualCasimirHeatCharacterSeries_apply
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatCharacterSeries data t g =
      ∑' q, (unitaryMatrixDualCasimirHeatCoefficientReal data t q : ℂ) *
        unitaryMatrixDualCharacter q g :=
  unitaryMatrixDualUniformCharacterSeries_apply _
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht) g

/-- At the identity, the spectral series is exactly the complex coercion of the supplied heat-trace
`tsum`. -/
theorem unitaryMatrixDualCasimirHeatCharacterSeries_one
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    unitaryMatrixDualCasimirHeatCharacterSeries data t (1 : G) =
      ∑' q, (((unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) : ℝ) : ℂ) := by
  rw [unitaryMatrixDualCasimirHeatCharacterSeries,
    unitaryMatrixDualUniformCharacterSeries_one _
      (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)]
  apply tsum_congr
  intro q
  rw [unitaryMatrixDualCasimirHeatCoefficient]
  norm_cast
  push_cast
  unfold unitaryMatrixDualCasimirHeatCoefficientReal
  ring

/-- The supplied real heat trace bounds the global uniform norm of the spectral series. -/
theorem norm_unitaryMatrixDualCasimirHeatCharacterSeries_le
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    ‖unitaryMatrixDualCasimirHeatCharacterSeries data t‖ ≤
      ∑' q, (unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) := by
  apply (norm_unitaryMatrixDualUniformCharacterSeries_le _
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht)).trans_eq
  apply tsum_congr
  intro q
  exact norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data t q

variable [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Normalized-Haar character analysis recovers the exact Casimir heat coefficient. -/
theorem normalizedCompactHaar_characterAnalysis_casimirHeatCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (q : UnitaryMatrixDual G) :
    (∫ g, star (unitaryMatrixDualCharacter q g) *
      unitaryMatrixDualCasimirHeatCharacterSeries data t g
      ∂normalizedCompactHaarMeasure G) =
      unitaryMatrixDualCasimirHeatCoefficient data t q :=
  normalizedCompactHaar_characterAnalysis_uniformCharacterSeries _
    (summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht) q

end

end Mathematics
end YangMills
