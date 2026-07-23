/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatCharacterSeries

/-!
# Uniform series of candidate Casimir heat-coefficient derivatives

Heat-trace summability at every positive time controls one additional Casimir factor at time `t` by
using the heat trace at `t/2`. Concretely,

`(c/2) exp (-(t/2)c) ≤ (2/t) exp (-(t/4)c)`.

This file uses that estimate to prove weighted unconditional uniform summability of the exact
coefficient derivatives

`-(c_q/2) dim(q) exp (-(t/2)c_q)`.

It constructs the resulting continuous central derivative-candidate series, its finite-subset net,
pointwise `tsum`, and a uniform norm bound. It also proves the derivative of each individual real
coefficient. It does **not** differentiate the original infinite character series; that interchange
remains a separate obligation.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Real derivative candidate for one Casimir heat coefficient. -/
noncomputable def unitaryMatrixDualCasimirHeatDerivativeCoefficientReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) : ℝ :=
  -(data.casimirWeight q / 2) *
    unitaryMatrixDualCasimirHeatCoefficientReal data t q

/-- Complex coercion of the derivative candidate. -/
noncomputable def unitaryMatrixDualCasimirHeatDerivativeCoefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) : ℂ :=
  (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q : ℂ)

/-- Elementary positive-time estimate which absorbs one spectral-weight factor by moving from time
`t` to `t/2`. -/
theorem casimir_mul_exp_neg_half_le
    (t c : ℝ) (ht : 0 < t) :
    (c / 2) * Real.exp (-(t / 2) * c) ≤
      (2 / t) * Real.exp (-((t / 2) / 2) * c) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hy : t * c / 4 ≤ Real.exp (t * c / 4) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hp : 0 < Real.exp (-(t * c / 2)) := Real.exp_pos _
  have hmul :
      (t * c / 4) * Real.exp (-(t * c / 2)) ≤
        Real.exp (t * c / 4) * Real.exp (-(t * c / 2)) :=
    mul_le_mul_of_nonneg_right hy hp.le
  rw [← Real.exp_add] at hmul
  rw [show t * c / 4 + -(t * c / 2) = -(t * c / 4) by ring] at hmul
  calc
    (c / 2) * Real.exp (-(t / 2) * c) =
        (2 / t) * ((t * c / 4) * Real.exp (-(t * c / 2))) := by
      field_simp
      ring
    _ ≤ (2 / t) * Real.exp (-(t * c / 4)) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = (2 / t) * Real.exp (-((t / 2) / 2) * c) := by
      congr 2
      ring

/-- Exact dimension-weighted norm of one derivative coefficient. -/
theorem norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) =
      (data.casimirWeight q / 2) *
        (unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-(t / 2) * data.casimirWeight q) := by
  unfold unitaryMatrixDualCasimirHeatDerivativeCoefficient
    unitaryMatrixDualCasimirHeatDerivativeCoefficientReal
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (div_nonneg (data.casimirWeight_nonneg q) (by norm_num)),
    abs_of_nonneg (unitaryMatrixDualCasimirHeatCoefficientReal_nonneg data t q)]
  unfold unitaryMatrixDualCasimirHeatCoefficientReal
  ring

/-- Heat-trace summability at time `t/2` gives weighted uniform summability of the exact derivative
coefficients at time `t`. -/
theorem summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun q =>
      ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ)) := by
  have hm : Summable (fun q => (2 / t) *
      ((unitaryMatrixDualDimension q : ℝ) ^ 2 *
        Real.exp (-((t / 2) / 2) * data.casimirWeight q))) :=
    (data.heatTrace_summable (t / 2) (half_pos ht)).mul_left (2 / t)
  refine Summable.of_nonneg_of_le
    (f := fun q => (2 / t) * ((unitaryMatrixDualDimension q : ℝ) ^ 2 *
      Real.exp (-((t / 2) / 2) * data.casimirWeight q)))
    (g := fun q => ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
      (unitaryMatrixDualDimension q : ℝ)) ?_ ?_ hm
  · intro q
    positivity
  · intro q
    rw [norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension]
    have hb := casimir_mul_exp_neg_half_le t (data.casimirWeight q) ht
    nlinarith [sq_nonneg (unitaryMatrixDualDimension q : ℝ)]

/-- Exact real derivative of each individual candidate Casimir heat coefficient. -/
theorem hasDerivAt_unitaryMatrixDualCasimirHeatCoefficientReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    HasDerivAt (fun s => unitaryMatrixDualCasimirHeatCoefficientReal data s q)
      (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q) t := by
  let w := data.casimirWeight q
  let d : ℝ := unitaryMatrixDualDimension q
  have hlin0 := (((hasDerivAt_id t).neg.div_const 2).mul_const w)
  have hlin : HasDerivAt (fun s : ℝ => -(s / 2) * w) (-(w / 2)) t :=
    (hlin0.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
      intro s
      change -(s / 2) * w = (-s) / 2 * w
      ring))).congr_deriv (by ring)
  have h0 := ((Real.hasDerivAt_exp (-(t / 2) * w)).comp t hlin).const_mul d
  have hevent :
      (fun s => unitaryMatrixDualCasimirHeatCoefficientReal data s q) =ᶠ[nhds t]
        (fun s => d * Real.exp (-(s / 2) * w)) := Filter.Eventually.of_forall (by
    intro s
    unfold unitaryMatrixDualCasimirHeatCoefficientReal
    rfl)
  have h1 := h0.congr_of_eventuallyEq hevent
  apply h1.congr_deriv
  unfold unitaryMatrixDualCasimirHeatDerivativeCoefficientReal
    unitaryMatrixDualCasimirHeatCoefficientReal
  dsimp only [w, d]
  ring

variable [CompactSpace G]

/-- Uniformly convergent continuous derivative-candidate character series. -/
noncomputable def unitaryMatrixDualCasimirHeatDerivativeCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) : C(G, ℂ) :=
  unitaryMatrixDualUniformCharacterSeries
    (unitaryMatrixDualCasimirHeatDerivativeCoefficient data t)

/-- Exact unconditional finite-subset convergence of the derivative-candidate series. -/
theorem tendsto_finsetSum_unitaryMatrixDualCasimirHeatDerivativeCharacter
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t)) :=
  tendsto_finsetSum_unitaryMatrixDualContinuousCharacter _
    (summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data ht)

/-- Exact pointwise unconditional `tsum` of coefficient derivatives times selected characters. -/
theorem unitaryMatrixDualCasimirHeatDerivativeCharacterSeries_apply
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t g =
      ∑' q, (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal data t q : ℂ) *
        unitaryMatrixDualCharacter q g :=
  unitaryMatrixDualUniformCharacterSeries_apply _
    (summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data ht) g

/-- Weierstrass norm bound for the derivative-candidate series. -/
theorem norm_unitaryMatrixDualCasimirHeatDerivativeCharacterSeries_le
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    ‖unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t‖ ≤
      ∑' q, ‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) :=
  norm_unitaryMatrixDualUniformCharacterSeries_le _
    (summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data ht)

end

end Mathematics
end YangMills
