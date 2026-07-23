/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatPositiveSemigroup

/-!
# Hostile probes for the positive Casimir heat-density semigroup
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatPositiveSemigroup
namespace Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Selected unitary characters transform under inversion by complex conjugation. -/
theorem exact_character_inversion (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualCharacter q g⁻¹ = star (unitaryMatrixDualCharacter q g) :=
  unitaryMatrixDualCharacter_inv_eq_star q g

variable [CompactSpace G]
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- The complex spectral series transforms under inversion by conjugation. -/
theorem exact_spectral_inversion {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g⁻¹ =
      star (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g) :=
  unitaryMatrixDualCasimirHeatCharacterSeries_inv heatTraceData ht g

/-- The real density is literally inversion invariant. -/
theorem exact_real_density_inversion {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g⁻¹ =
      unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g :=
  unitaryMatrixDualCasimirHeatDensityReal_inv heatTraceData ht g

/-- Hostile inversion probe. -/
theorem changed_real_density_inversion_blocked
    {t : ℝ} (ht : 0 < t) (g : G) (changed : ℝ)
    (hchanged : changed ≠ unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g)
    (changedInversion : unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g⁻¹ =
      changed) : False := by
  apply hchanged
  rw [← changedInversion]
  exact unitaryMatrixDualCasimirHeatDensityReal_inv heatTraceData ht g

variable [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Under positivity, the real density has the exact source-facing convolution law. -/
theorem exact_real_density_add
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) :
    unitaryMatrixDualCasimirHeatDensityReal heatTraceData (s + t) z =
      ∫ x, unitaryMatrixDualCasimirHeatDensityReal heatTraceData s x *
        unitaryMatrixDualCasimirHeatDensityReal heatTraceData t (x⁻¹ * z)
        ∂normalizedCompactHaarMeasure G :=
  normalizedCompactHaar_integral_casimirHeatDensityReal_mul
    heatTraceData positivity hs ht z

/-- Under positivity, the `ENNReal` density has the exact two-dimensional convolution law. -/
theorem exact_ennreal_density_add
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) :
    unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (s + t) z =
      normalizedCompactHaarDensityConvolution G
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData s)
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t) z :=
  unitaryMatrixDualCasimirHeatDensityENNReal_add heatTraceData positivity hs ht z

/-- Hostile semigroup probe: a changed positive density-addition value is contradictory. -/
theorem changed_ennreal_density_add_blocked
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) (changed : ENNReal)
    (hchanged : changed ≠ normalizedCompactHaarDensityConvolution G
      (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData s)
      (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t) z)
    (changedAddition : unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (s + t) z =
      changed) : False := by
  apply hchanged
  rw [← changedAddition]
  exact unitaryMatrixDualCasimirHeatDensityENNReal_add heatTraceData positivity hs ht z

end

end Probes
end UnitaryMatrixDualCasimirHeatPositiveSemigroup
end Mathematics
end YangMills
