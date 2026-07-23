/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatPositivity

/-!
# Hostile probes for candidate Casimir heat positivity
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatPositivity
namespace Probes

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

omit [CompactSpace G] in
/-- Positivity data expose exact real-valuedness at every positive time. -/
theorem exact_imaginary_part_zero
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (g : G) :
    (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g).im = 0 :=
  positivity.value_im_zero t ht g

omit [CompactSpace G] in
/-- Positivity data expose strict positivity of the real part. -/
theorem exact_real_part_positive
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (g : G) :
    0 < (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g).re :=
  positivity.value_re_pos t ht g

omit [CompactSpace G] in
/-- The complex spectral value is exactly the coercion of its positive real density. -/
theorem exact_complex_value_eq_real_density
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g =
      (unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g : ℂ) :=
  unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal heatTraceData positivity ht g

omit [CompactSpace G] in
/-- Hostile real-valuedness probe: a nonzero imaginary part contradicts positivity data. -/
theorem nonreal_value_blocked
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (g : G)
    (nonreal : (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g).im ≠ 0) : False :=
  nonreal (positivity.value_im_zero t ht g)

omit [CompactSpace G] in
/-- Hostile positivity probe: a nonpositive real density contradicts positivity data. -/
theorem nonpositive_value_blocked
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (g : G)
    (nonpositive : unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g ≤ 0) : False :=
  (not_le_of_gt (unitaryMatrixDualCasimirHeatDensityReal_pos
    heatTraceData positivity ht g)) nonpositive

variable [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}

/-- The positive `ENNReal` density has normalized Haar lintegral one under the bridge. -/
theorem exact_ennreal_density_mass
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ g, unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t g
      ∂normalizedCompactHaarMeasure G) = 1 :=
  normalizedCompactHaar_lintegral_casimirHeatDensityENNReal bridge positivity ht

/-- The associated positive-time with-density measure has total mass one. -/
theorem exact_probability_measure_mass
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t Set.univ = 1 :=
  unitaryMatrixDualCasimirHeatProbabilityMeasure_univ bridge positivity ht

/-- Hostile probability-mass probe. -/
theorem changed_probability_measure_mass_blocked
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) (changed : ENNReal) (hchanged : changed ≠ 1)
    (changedMass : unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t Set.univ =
      changed) : False := by
  apply hchanged
  rw [← changedMass]
  exact unitaryMatrixDualCasimirHeatProbabilityMeasure_univ bridge positivity ht

end

end Probes
end UnitaryMatrixDualCasimirHeatPositivity
end Mathematics
end YangMills
