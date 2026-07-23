/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatPositivity

/-!
# Explicit weak time-zero identity debt for the candidate spectral family

Lévy §1.4 requires the positive-time fundamental solution to converge weakly to the identity:

`∫ f(g) p_t(g) dg → f(1)` as `t → 0+`

for every continuous test function. The existing positive-time spectral assumptions do not imply
this limit. This file therefore records it exactly as uninhabited
`UnitaryMatrixDualCasimirHeatInitialIdentityData` using the filter
`𝓝[Set.Ioi 0] 0`.

Under the separately uninhabited positivity data, integration against the positive `ENNReal`
with-density measure is proved equal to integration against the original complex spectral series.
The supplied weak identity then transports to those measures. Combined separately with the
geometric bridge, their total mass is one.

No initial-identity datum, time-zero density, Brownian motion, or heat kernel is constructed.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Exact weak convergence to identity required of the candidate positive-time spectral family.
This is caller-supplied uninhabited data. -/
structure UnitaryMatrixDualCasimirHeatInitialIdentityData
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) where
  weak_identity : ∀ f : C(G, ℂ),
    Filter.Tendsto
      (fun t : ℝ => ∫ g, f g * unitaryMatrixDualCasimirHeatCharacterSeries data t g
        ∂normalizedCompactHaarMeasure G)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1))

omit [T2Space G] in
/-- At positive time, integration against the `ENNReal` with-density measure is exactly integration
against the real-valued complex spectral density. -/
theorem integral_casimirHeatProbabilityMeasure_eq_integral_characterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {t : ℝ} (ht : 0 < t) (f : C(G, ℂ)) :
    (∫ g, f g ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t) =
      ∫ g, f g * unitaryMatrixDualCasimirHeatCharacterSeries data t g
        ∂normalizedCompactHaarMeasure G := by
  rw [unitaryMatrixDualCasimirHeatProbabilityMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_unitaryMatrixDualCasimirHeatDensityENNReal data t)]
  · apply integral_congr_ae
    filter_upwards [] with g
    rw [unitaryMatrixDualCasimirHeatDensityENNReal, ENNReal.toReal_ofReal
      (unitaryMatrixDualCasimirHeatDensityReal_pos data positivity ht g).le]
    rw [unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal data positivity ht g]
    change (unitaryMatrixDualCasimirHeatDensityReal data t g : ℂ) * f g =
      f g * (unitaryMatrixDualCasimirHeatDensityReal data t g : ℂ)
    ring
  · filter_upwards [] with g
    exact ENNReal.ofReal_lt_top

omit [T2Space G] in
/-- The supplied weak identity transports exactly to expectations under the positive with-density
measures. Their mass-one property remains the separate geometric-bridge theorem. -/
theorem tendsto_integral_casimirHeatProbabilityMeasure_nhdsWithin_zero
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    (initial : UnitaryMatrixDualCasimirHeatInitialIdentityData data)
    (f : C(G, ℂ)) :
    Filter.Tendsto
      (fun t : ℝ => ∫ g, f g ∂unitaryMatrixDualCasimirHeatProbabilityMeasure data t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1)) := by
  apply (initial.weak_identity f).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_casimirHeatProbabilityMeasure_eq_integral_characterSeries
    data positivity ht f).symm

end

end Mathematics
end YangMills
