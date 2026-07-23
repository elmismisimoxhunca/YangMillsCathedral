/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirLaplacianBridge

/-!
# Hostile probes for the candidate Casimir/geometric-Laplacian bridge
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirLaplacianBridge
namespace Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- The bridge supplies actual manifold smoothness of every selected character. -/
theorem exact_character_smoothness
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) ∞
      (unitaryMatrixDualCharacter q) :=
  bridge.character_contMDiff q

/-- The signed eigenvalue equation is exactly `Δχ_q = -c_qχ_q`. -/
theorem exact_signed_character_eigenvalue
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (g : G) :
    laplacianData.laplacian (bridge.smoothCharacter q) g =
      -(heatTraceData.casimirWeight q : ℂ) * unitaryMatrixDualCharacter q g :=
  bridge.laplacian_smoothCharacter q g

/-- Hostile sign probe: replacing `-c_q` by `+c_q` is rejected whenever those values differ. -/
theorem changed_eigenvalue_sign_blocked
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (g : G)
    (signDifferent : (heatTraceData.casimirWeight q : ℂ) *
      unitaryMatrixDualCharacter q g ≠
      -(heatTraceData.casimirWeight q : ℂ) * unitaryMatrixDualCharacter q g)
    (changedSign : laplacianData.laplacian (bridge.smoothCharacter q) g =
      (heatTraceData.casimirWeight q : ℂ) * unitaryMatrixDualCharacter q g) : False := by
  apply signDifferent
  rw [← changedSign]
  exact bridge.laplacian_smoothCharacter q g

/-- Any real candidate satisfying the same character equation for the fixed Laplacian equals the
stored candidate Casimir weight. -/
theorem exact_eigenvalue_uniqueness
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (candidate : ℝ)
    (candidateEquation : ∀ g : G,
      laplacianData.laplacian (bridge.smoothCharacter q) g =
        -(candidate : ℂ) * unitaryMatrixDualCharacter q g) :
    candidate = heatTraceData.casimirWeight q :=
  bridge.casimirWeight_eq_of_character_laplacian q candidate candidateEquation

/-- Hostile weight probe: a genuinely changed real weight cannot satisfy the same eigenvalue
equation. -/
theorem changed_eigenvalue_blocked
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (changed : ℝ)
    (hchanged : changed ≠ heatTraceData.casimirWeight q)
    (changedEquation : ∀ g : G,
      laplacianData.laplacian (bridge.smoothCharacter q) g =
        -(changed : ℂ) * unitaryMatrixDualCharacter q g) : False :=
  hchanged (bridge.casimirWeight_eq_of_character_laplacian q changed changedEquation)

/-- The candidate coefficient has the exact `-(c_q/2)` logarithmic derivative. -/
theorem exact_heat_coefficient_derivative
    (t : ℝ) (q : UnitaryMatrixDual G) :
    HasDerivAt (fun s =>
      unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData s q)
      (-(heatTraceData.casimirWeight q / 2) *
        unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q) t :=
  hasDerivAt_unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q

/-- Hostile derivative probe: a changed derivative value is contradictory. -/
theorem changed_heat_coefficient_derivative_blocked
    (t : ℝ) (q : UnitaryMatrixDual G) (changed : ℝ)
    (hchanged : changed ≠ -(heatTraceData.casimirWeight q / 2) *
      unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q)
    (changedDerivative : HasDerivAt (fun s =>
      unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData s q) changed t) : False := by
  apply hchanged
  exact HasDerivAt.unique changedDerivative
    (hasDerivAt_unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q)

/-- The single-character term has the exact `1/2` heat-equation multiplier and no infinite-series
interchange. -/
theorem exact_termwise_half_laplacian
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (t : ℝ) (q : UnitaryMatrixDual G) (g : G) :
    ((-(heatTraceData.casimirWeight q / 2) *
        unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q : ℝ) : ℂ) *
        unitaryMatrixDualCharacter q g =
      (1 / 2 : ℂ) *
        (unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q : ℂ) *
        laplacianData.laplacian (bridge.smoothCharacter q) g :=
  unitaryMatrixDualCasimirHeatTerm_derivative_eq_half_laplacian bridge t q g

end

end Probes
end UnitaryMatrixDualCasimirLaplacianBridge
end Mathematics
end YangMills
