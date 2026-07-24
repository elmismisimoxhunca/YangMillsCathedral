/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatDensitySemigroup

/-!
# Hostile probes for the conditional Casimir density semigroup

These checks ensure that the assembled interface retains the exact spectral density, normalized
Haar convolution orientation, positive-time nonzero measure, and weak identity limit.
-/

namespace YangMills.Mathematics

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uG uE

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
  {inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)}
  {laplacianData : RightInvariantPairingComplexLaplacianData inner}
  {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
  (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
    inner laplacianData heatTraceData)
  (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
  (initial : UnitaryMatrixDualCasimirHeatInitialIdentityData heatTraceData)

include bridge positivity initial

/-- The constructor lands in the exact generic density-semigroup interface without replacing the
spectral family. -/
noncomputable def exact_casimirHeatDensitySemigroup :
    NormalizedCompactHaarDensitySemigroupData
      (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData) :=
  unitaryMatrixDualCasimirHeatDensitySemigroupData bridge positivity initial

/-- Every assembled positive-time spectral measure is nonzero. -/
theorem exact_casimirHeatDensitySemigroup_measure_ne_zero
    {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure
      (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData) t ≠ 0 :=
  (unitaryMatrixDualCasimirHeatDensitySemigroupData bridge positivity initial).measure_ne_zero ht

/-- Hostile orientation probe: changing the proved source-facing convolution equation is rejected. -/
theorem changed_casimirHeatDensitySemigroup_add_blocked
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : G)
    (changed : unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (s + t) g ≠
      normalizedCompactHaarDensityConvolution G
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData s)
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t) g) : False :=
  changed ((unitaryMatrixDualCasimirHeatDensitySemigroupData bridge positivity initial).density_add
    s t hs ht g)

/-- Hostile weak-limit probe: the assembled family cannot converge to a changed value for one
continuous test. -/
theorem changed_casimirHeatDensitySemigroup_weak_limit_blocked
    (f : C(G, ℂ)) (z : ℂ)
    (changed : Filter.Tendsto
      (fun t : ℝ => ∫ g, f g
        ∂((normalizedCompactHaarMeasure G).withDensity
          (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds z))
    (hz : z ≠ f 1) : False :=
  hz (tendsto_nhds_unique changed
    ((unitaryMatrixDualCasimirHeatDensitySemigroupData bridge positivity initial)
      |>.weak_tendsto_identity f))

end

end YangMills.Mathematics
