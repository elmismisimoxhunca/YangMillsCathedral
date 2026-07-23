/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatEquation

/-!
# Hostile probes for the formal Casimir heat equation
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCasimirHeatEquation
namespace Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The formal Laplacian coefficient is exactly `-c_q` times the heat coefficient. -/
theorem exact_laplacian_coefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatLaplacianCoefficientReal data t q =
      -data.casimirWeight q * unitaryMatrixDualCasimirHeatCoefficientReal data t q :=
  rfl

/-- The formal Laplacian coefficient is exactly twice the derivative coefficient. -/
theorem exact_laplacian_coefficient_eq_two_derivative
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q =
      2 * unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q :=
  unitaryMatrixDualCasimirHeatLaplacianCoefficient_eq_two_derivative data t q

/-- Hostile coefficient probe: changing the exact doubled derivative value is contradictory. -/
theorem changed_laplacian_coefficient_blocked
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) (changed : ℂ)
    (hchanged : changed ≠ 2 * unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q)
    (changedCoefficient : unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q = changed) : False := by
  apply hchanged
  rw [← changedCoefficient]
  exact unitaryMatrixDualCasimirHeatLaplacianCoefficient_eq_two_derivative data t q

/-- Positive-time formal Laplacian coefficients satisfy the required weighted summability. -/
theorem exact_laplacian_coefficient_summability
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun q => ‖unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q‖ *
      (unitaryMatrixDualDimension q : ℝ)) :=
  summable_norm_unitaryMatrixDualCasimirHeatLaplacianCoefficient_mul_dimension data ht

variable [CompactSpace G]

/-- The formal Laplacian series is exactly twice the derivative-candidate series. -/
theorem exact_laplacian_series_eq_two_derivative
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    unitaryMatrixDualCasimirHeatLaplacianCharacterSeries data t =
      (2 : ℂ) • unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t :=
  unitaryMatrixDualCasimirHeatLaplacianCharacterSeries_eq_two_derivative data ht

/-- Formal Laplacian finite-subset sums converge unconditionally in the global uniform norm. -/
theorem exact_laplacian_finset_net
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualCasimirHeatLaplacianCharacterSeries data t)) :=
  tendsto_finsetSum_unitaryMatrixDualCasimirHeatLaplacianCharacter data ht

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData}

omit [CompactSpace G] in
/-- Interchange data expose actual smoothness of the infinite positive-time spectral sum. -/
theorem exact_interchanged_spatial_smoothness
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) ∞
      (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t) :=
  interchange.heatSeries_contMDiff t ht

omit [CompactSpace G] in
/-- The Laplacian interchange is tied to the exact formal Laplacian series. -/
theorem exact_laplacian_interchange
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) (g : G) :
    laplacianData.laplacian (interchange.smoothHeatCharacterSeries t ht) g =
      unitaryMatrixDualCasimirHeatLaplacianCharacterSeries heatTraceData t g := by
  exact interchange.laplacian_interchange t ht g

omit [CompactSpace G] in
/-- The time-derivative interchange is tied to the already constructed derivative-candidate
series. -/
theorem exact_time_derivative_interchange
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData s g)
      (unitaryMatrixDualCasimirHeatDerivativeCharacterSeries heatTraceData t g) t :=
  interchange.timeDerivative_interchange t ht g

/-- With exactly the explicit interchange data, the pointwise positive-time heat equation follows. -/
theorem exact_conditional_heat_equation
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData s g)
      ((1 / 2 : ℂ) * laplacianData.laplacian
        (interchange.smoothHeatCharacterSeries t ht) g) t :=
  interchange.hasDerivAt_heatCharacterSeries_eq_half_laplacian t ht g

/-- Hostile heat-equation probe: a genuinely changed pointwise derivative is contradictory once the
interchange data are supplied. -/
theorem changed_conditional_heat_equation_blocked
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) (g : G) (changed : ℂ)
    (hchanged : changed ≠ (1 / 2 : ℂ) * laplacianData.laplacian
      (interchange.smoothHeatCharacterSeries t ht) g)
    (changedDerivative : HasDerivAt
      (fun s => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData s g) changed t) : False := by
  apply hchanged
  exact HasDerivAt.unique changedDerivative
    (interchange.hasDerivAt_heatCharacterSeries_eq_half_laplacian t ht g)

end

end Probes
end UnitaryMatrixDualCasimirHeatEquation
end Mathematics
end YangMills
