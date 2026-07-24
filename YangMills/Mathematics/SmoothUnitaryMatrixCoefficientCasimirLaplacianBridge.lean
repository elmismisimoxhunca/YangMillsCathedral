/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantRealComplexLaplacianCoherence
import YangMills.Mathematics.LieGroupRightInvariantScalarDerivativeSmoothness
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientRealCore
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatDerivativeSeries

/-!
# Matrix-coefficient Casimir/Laplacian bridge

The existing character bridge identifies only traces with candidate Casimir weights. That does not
imply the corresponding equation for each matrix coordinate. This file exposes the stronger
coefficientwise identification as a separate uninhabited bridge indexed by explicit smooth
irreducible presentations.

From that bridge, canonical real/complex Laplacian coherence proves the exact eigenvalue equation
for both real components, and linearity gives the coefficientwise Laplacian on every finite real
synthesis. No bridge inhabitant, heat action, generator limit, graph density, or Peter--Weyl theorem
is constructed.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Explicit unresolved coefficientwise identification of the selected candidate Casimir weight
with the pairing-normalized complex right-invariant Laplacian. -/
structure SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    (complexLaplacian : RightInvariantPairingComplexLaplacianData inner)
    (heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) where
  coefficient_laplacian :
    ∀ (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
      (row column : Fin ρ.dimension) (g : G),
      complexLaplacian.laplacian
        (smoothUnitaryMatrixCoefficient ρ row column) g =
        -(heatTraceData.casimirWeight
          (unitaryMatrixDualClass
            ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) : ℂ) *
          ρ.representation g row column

namespace SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData

/-- Restatement of the stored complex coefficient eigenvalue equation. -/
theorem laplacian_smoothCoefficient
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    complexLaplacian.laplacian
      (smoothUnitaryMatrixCoefficient ρ row column) g =
      -(heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) : ℂ) *
        smoothUnitaryMatrixCoefficient ρ row column g :=
  bridge.coefficient_laplacian ρ row column g

/-- Canonical real/complex coherence transports the coefficientwise Casimir equation to either real
scalar component. -/
theorem laplacian_smoothRealCoefficient
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (realLaplacian : RightInvariantPairingLaplacianData inner)
    (complexLaplacian : RightInvariantPairingComplexLaplacianData inner)
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) (g : G) :
    realLaplacian.laplacian
      (smoothUnitaryMatrixCoefficientRealFunction index) g =
      -(heatTraceData.casimirWeight
        (unitaryMatrixDualClass
          index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) *
        smoothUnitaryMatrixCoefficientRealFunction index g := by
  let coherence := rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian
  rcases index with ⟨ρ, row, column, component⟩
  cases component with
  | real =>
      rw [show realLaplacian.laplacian
        (smoothUnitaryMatrixCoefficientRealFunction ⟨ρ, row, column, .real⟩) g =
          (complexLaplacian.laplacian
            (smoothUnitaryMatrixCoefficient ρ row column) g).re from
        coherence.laplacian_realPart
          (smoothUnitaryMatrixCoefficient ρ row column) g]
      rw [bridge.laplacian_smoothCoefficient]
      simp [Complex.mul_re]
  | imaginary =>
      rw [show realLaplacian.laplacian
        (smoothUnitaryMatrixCoefficientRealFunction ⟨ρ, row, column, .imaginary⟩) g =
          (complexLaplacian.laplacian
            (smoothUnitaryMatrixCoefficient ρ row column) g).im from
        coherence.laplacian_imaginaryPart
          (smoothUnitaryMatrixCoefficient ρ row column) g]
      rw [bridge.laplacian_smoothCoefficient]
      simp [Complex.mul_im]

/-- The candidate real Casimir eigenvalue is unique: evaluate any diagonal coefficient at the group
identity, where it is exactly one. -/
theorem casimirWeight_eq_of_diagonal_coefficient_laplacian
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row : Fin ρ.dimension) (candidate : ℝ)
    (candidateEquation : ∀ g : G,
      complexLaplacian.laplacian
        (smoothUnitaryMatrixCoefficient ρ row row) g =
        -(candidate : ℂ) * ρ.representation g row row) :
    candidate = heatTraceData.casimirWeight
      (unitaryMatrixDualClass
        ρ.toContinuousUnitaryIrreducibleMatrixRepresentation) := by
  have equality := (candidateEquation (1 : G)).symm.trans
    (bridge.laplacian_smoothCoefficient ρ row row 1)
  simp at equality
  exact equality

/-- Finite synthesis of the coefficientwise real Laplacian eigenvalues. -/
noncomputable def smoothUnitaryMatrixCoefficientRealLaplacianSynthesis
    (heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) :
    SmoothUnitaryMatrixCoefficientRealCoefficients E G →ₗ[ℝ]
      SmoothLieGroupScalarFunction (E := E) (G := G) :=
  Finsupp.linearCombination ℝ (fun index =>
    -(heatTraceData.casimirWeight
      (unitaryMatrixDualClass
        index.representation.toContinuousUnitaryIrreducibleMatrixRepresentation)) •
      smoothUnitaryMatrixCoefficientRealFunction index)

/-- The canonical real pairing Laplacian acts coefficientwise on every finite real smooth matrix-
coefficient synthesis. -/
theorem rightInvariantPairingLaplacianLinearMap_comp_coefficientSynthesis
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (realLaplacian : RightInvariantPairingLaplacianData inner)
    (complexLaplacian : RightInvariantPairingComplexLaplacianData inner)
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData) :
    (rightInvariantPairingLaplacianLinearMap realLaplacian).comp
        smoothUnitaryMatrixCoefficientRealSynthesis =
      smoothLieGroupScalarToContinuousLinearMap.comp
        (smoothUnitaryMatrixCoefficientRealLaplacianSynthesis heatTraceData) := by
  apply Finsupp.lhom_ext
  intro index coefficient
  ext g
  simp only [LinearMap.comp_apply, smoothUnitaryMatrixCoefficientRealSynthesis,
    smoothUnitaryMatrixCoefficientRealLaplacianSynthesis,
    Finsupp.linearCombination_single, map_smul,
    ContinuousMap.smul_apply, smul_eq_mul,
    rightInvariantPairingLaplacianLinearMap_apply,
    smoothLieGroupScalarToContinuousLinearMap_apply]
  rw [bridge.laplacian_smoothRealCoefficient realLaplacian complexLaplacian]

end SmoothUnitaryMatrixCoefficientCasimirLaplacianBridgeData

end

end Mathematics
end YangMills
