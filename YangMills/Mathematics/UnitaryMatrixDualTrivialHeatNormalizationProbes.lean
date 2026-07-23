/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualTrivialHeatNormalization

/-!
# Hostile probes for trivial-class spectral normalization
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualTrivialHeatNormalization
namespace Probes

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The explicit selected trivial character is exactly one everywhere. -/
theorem exact_trivial_character (g : G) :
    unitaryMatrixDualCharacter (unitaryMatrixDualTrivialClass G) g = 1 :=
  unitaryMatrixDualCharacter_trivialClass g

/-- The selected trivial-class representation dimension is exactly one. -/
theorem exact_trivial_dimension :
    unitaryMatrixDualDimension (unitaryMatrixDualTrivialClass G) = 1 :=
  unitaryMatrixDualDimension_trivialClass

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- The geometric bridge forces the trivial-class candidate weight to zero. -/
theorem exact_trivial_casimir_weight
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData) :
    heatTraceData.casimirWeight (unitaryMatrixDualTrivialClass G) = 0 :=
  unitaryMatrixDualCasimirWeight_trivialClass bridge

/-- Hostile trivial-weight probe: any asserted nonzero trivial-class weight is contradictory. -/
theorem nonzero_trivial_casimir_weight_blocked
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (nonzero : heatTraceData.casimirWeight (unitaryMatrixDualTrivialClass G) ≠ 0) : False :=
  nonzero (unitaryMatrixDualCasimirWeight_trivialClass bridge)

/-- The trivial-class heat coefficient is exactly one at every real time. -/
theorem exact_trivial_heat_coefficient
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (t : ℝ) :
    unitaryMatrixDualCasimirHeatCoefficient heatTraceData t
      (unitaryMatrixDualTrivialClass G) = 1 :=
  unitaryMatrixDualCasimirHeatCoefficient_trivialClass bridge t

/-- Hostile coefficient probe: a changed trivial-class heat coefficient is contradictory. -/
theorem changed_trivial_heat_coefficient_blocked
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (t : ℝ) (changed : ℂ) (hchanged : changed ≠ 1)
    (changedCoefficient : unitaryMatrixDualCasimirHeatCoefficient heatTraceData t
      (unitaryMatrixDualTrivialClass G) = changed) : False := by
  apply hchanged
  rw [← changedCoefficient]
  exact unitaryMatrixDualCasimirHeatCoefficient_trivialClass bridge t

variable [CompactSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Exact conditional normalized-Haar mass one for the candidate spectral series. -/
theorem exact_normalized_haar_mass
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    (∫ g, unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g
      ∂normalizedCompactHaarMeasure G) = 1 :=
  normalizedCompactHaar_integral_casimirHeatCharacterSeries bridge ht

/-- Hostile normalization probe: a genuinely changed normalized-Haar mass is contradictory. -/
theorem changed_normalized_haar_mass_blocked
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    {t : ℝ} (ht : 0 < t) (changed : ℂ) (hchanged : changed ≠ 1)
    (changedMass : (∫ g, unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g
      ∂normalizedCompactHaarMeasure G) = changed) : False := by
  apply hchanged
  rw [← changedMass]
  exact normalizedCompactHaar_integral_casimirHeatCharacterSeries bridge ht

end

end Probes
end UnitaryMatrixDualTrivialHeatNormalization
end Mathematics
end YangMills
