/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatInitialIdentity

/-!
# Hostile probes for weak time-zero identity convergence
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatInitialIdentity
namespace Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

omit [T2Space G] in
/-- The exact source limit uses the positive-side neighborhood filter and evaluation at identity. -/
theorem exact_weak_identity
    (initial : UnitaryMatrixDualCasimirHeatInitialIdentityData heatTraceData)
    (f : C(G, ℂ)) :
    Filter.Tendsto
      (fun t : ℝ => ∫ g, f g *
        unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g
        ∂normalizedCompactHaarMeasure G)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1)) :=
  initial.weak_identity f

omit [T2Space G] in
/-- Positive with-density expectations retain the exact complex spectral integral. -/
theorem exact_positive_measure_integral
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (f : C(G, ℂ)) :
    (∫ g, f g ∂unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t) =
      ∫ g, f g * unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g
        ∂normalizedCompactHaarMeasure G :=
  integral_casimirHeatProbabilityMeasure_eq_integral_characterSeries
    heatTraceData positivity ht f

omit [T2Space G] in
/-- Weak identity convergence transports to the positive with-density measures. -/
theorem exact_positive_measure_weak_identity
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    (initial : UnitaryMatrixDualCasimirHeatInitialIdentityData heatTraceData)
    (f : C(G, ℂ)) :
    Filter.Tendsto
      (fun t : ℝ => ∫ g, f g
        ∂unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1)) :=
  tendsto_integral_casimirHeatProbabilityMeasure_nhdsWithin_zero
    heatTraceData positivity initial f

omit [T2Space G] in
/-- Hostile limit probe: a genuinely changed weak identity limit is contradictory. -/
theorem changed_weak_identity_limit_blocked
    (initial : UnitaryMatrixDualCasimirHeatInitialIdentityData heatTraceData)
    (f : C(G, ℂ)) (changed : ℂ) (hchanged : changed ≠ f 1)
    (changedLimit : Filter.Tendsto
      (fun t : ℝ => ∫ g, f g *
        unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g
        ∂normalizedCompactHaarMeasure G)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds changed)) : False := by
  apply hchanged
  exact tendsto_nhds_unique changedLimit (initial.weak_identity f)

end

end Probes
end UnitaryMatrixDualCasimirHeatInitialIdentity
end Mathematics
end YangMills
