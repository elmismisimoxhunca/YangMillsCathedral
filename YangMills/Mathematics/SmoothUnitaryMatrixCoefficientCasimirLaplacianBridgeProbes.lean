/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientCasimirLaplacianBridge

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

open SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
  {inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)}
  (realLaplacian : RightInvariantPairingLaplacianData inner)
  (complexLaplacian : RightInvariantPairingComplexLaplacianData inner)
  {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
  (bridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
    inner complexLaplacian heatTraceData)

include bridge in
/-- Exact complex coefficientwise Casimir equation probe. -/
theorem exact_smoothMatrixCoefficient_casimirLaplacian
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    complexLaplacian.laplacian
      (smoothUnitaryMatrixCoefficient ρ row column) g =
      -(heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) : ℂ) *
        ρ.representation g row column :=
  laplacian_smoothCoefficient bridge ρ row column g

include bridge in
/-- Exact real/imaginary coefficientwise Casimir equation probe. -/
theorem exact_smoothRealMatrixCoefficient_casimirLaplacian
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) :
    realLaplacian.laplacian
      (smoothUnitaryMatrixCoefficientRealFunction index) g =
      -(heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g :=
  laplacian_smoothRealCoefficient realLaplacian complexLaplacian bridge index g

include bridge in
/-- Exact finite-synthesis probe: the real pairing Laplacian acts coefficientwise. -/
theorem exact_smoothMatrixCoefficient_finiteLaplacian
    (coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    rightInvariantPairingLaplacianLinearMap realLaplacian
        (smoothUnitaryMatrixCoefficientRealSynthesis coefficients) =
      smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientRealLaplacianSynthesis
          heatTraceData coefficients) := by
  have maps := rightInvariantPairingLaplacianLinearMap_comp_coefficientSynthesis
    realLaplacian complexLaplacian bridge
  exact LinearMap.congr_fun maps coefficients

include bridge in
/-- Exact uniqueness probe from one diagonal coefficient at the identity. -/
theorem exact_smoothMatrixCoefficient_casimirWeight_unique
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row : Fin ρ.dimension) (candidate : ℝ)
    (candidateEquation : ∀ g : G,
      complexLaplacian.laplacian
        (smoothUnitaryMatrixCoefficient ρ row row) g =
        -(candidate : ℂ) * ρ.representation g row row) :
    candidate = heatTraceData.casimirWeight
      (unitaryMatrixDualClass
        ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) :=
  casimirWeight_eq_of_diagonal_coefficient_laplacian
    bridge ρ row candidate candidateEquation

include bridge in
/-- Hostile coefficientwise eigenvalue probe: a changed Laplacian value is contradictory. -/
theorem changed_smoothMatrixCoefficient_casimirLaplacian_blocked
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) (changed : ℂ)
    (changed_ne_exact : changed ≠
      -(heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) : ℂ) *
        ρ.representation g row column)
    (claimed : complexLaplacian.laplacian
      (smoothUnitaryMatrixCoefficient ρ row column) g = changed) : False := by
  apply changed_ne_exact
  rw [← claimed]
  exact laplacian_smoothCoefficient bridge ρ row column g

end

end Mathematics
end YangMills
