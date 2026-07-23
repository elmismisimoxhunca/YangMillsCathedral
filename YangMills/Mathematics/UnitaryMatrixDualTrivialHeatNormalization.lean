/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupSelectedDualDensity
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatEquation

/-!
# Trivial selected class and conditional Haar normalization of the spectral series

This file names the selected unitary-dual class of the explicit one-dimensional trivial
representation. Its selected character is exactly one and its selected dimension is exactly one.
For any inhabitant of the explicit Casimir/Laplacian bridge, the equation

`Δ 1 = -c_triv · 1`

forces the trivial-class candidate weight to be zero. Consequently the candidate heat coefficient
at the trivial class is one. Exact normalized-Haar character analysis then proves

`∫ K_t dμ_H = 1`

for every positive time.

This is conditional on the still-uninhabited geometric bridge and heat-trace data. It proves no
pointwise positivity, time-zero identity, interchange inhabitant, or heat-kernel status.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Selected unitary-dual class of the explicit one-dimensional trivial representation. -/
noncomputable def unitaryMatrixDualTrivialClass (G : Type uG)
    [Group G] [TopologicalSpace G] : UnitaryMatrixDual G :=
  unitaryMatrixDualClass (trivialContinuousUnitaryIrreducibleMatrixRepresentation G)

/-- The selected character of the trivial class is exactly the constant one function. -/
@[simp]
theorem unitaryMatrixDualCharacter_trivialClass (g : G) :
    unitaryMatrixDualCharacter (unitaryMatrixDualTrivialClass G) g = 1 := by
  unfold unitaryMatrixDualTrivialClass
  rw [unitaryMatrixDualCharacter_class_eq]
  simp [trivialContinuousUnitaryIrreducibleMatrixRepresentation,
    trivialOneDimensionalMatrixRepresentation, Matrix.trace]
  change (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1
  simp

/-- The selected representative of the trivial class has dimension exactly one. -/
@[simp]
theorem unitaryMatrixDualDimension_trivialClass :
    unitaryMatrixDualDimension (unitaryMatrixDualTrivialClass G) = 1 := by
  have h := unitaryMatrixDualCharacter_one (unitaryMatrixDualTrivialClass G)
  rw [unitaryMatrixDualCharacter_trivialClass] at h
  exact_mod_cast h.symm

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- The bridge forces the candidate Casimir weight of the trivial class to vanish. -/
theorem unitaryMatrixDualCasimirWeight_trivialClass
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData) :
    heatTraceData.casimirWeight (unitaryMatrixDualTrivialClass G) = 0 := by
  let q := unitaryMatrixDualTrivialClass G
  have hsc : bridge.smoothCharacter q = SmoothLieGroupComplexFunction.const 1 := by
    apply SmoothLieGroupComplexFunction.ext
    funext g
    exact unitaryMatrixDualCharacter_trivialClass g
  have he := bridge.laplacian_smoothCharacter q (1 : G)
  rw [hsc, RightInvariantPairingComplexLaplacianData.laplacian_const] at he
  dsimp only [q] at he
  simp only [unitaryMatrixDualCharacter_trivialClass, mul_one] at he
  have hc : (heatTraceData.casimirWeight (unitaryMatrixDualTrivialClass G) : ℂ) = 0 := by
    simpa using he.symm
  exact_mod_cast hc

/-- The real candidate heat coefficient of the trivial class is exactly one at every time. -/
theorem unitaryMatrixDualCasimirHeatCoefficientReal_trivialClass
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (t : ℝ) :
    unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t
      (unitaryMatrixDualTrivialClass G) = 1 := by
  unfold unitaryMatrixDualCasimirHeatCoefficientReal
  rw [unitaryMatrixDualDimension_trivialClass,
    unitaryMatrixDualCasimirWeight_trivialClass bridge]
  norm_num

/-- The complex candidate heat coefficient of the trivial class is exactly one. -/
theorem unitaryMatrixDualCasimirHeatCoefficient_trivialClass
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (t : ℝ) :
    unitaryMatrixDualCasimirHeatCoefficient heatTraceData t
      (unitaryMatrixDualTrivialClass G) = 1 := by
  rw [unitaryMatrixDualCasimirHeatCoefficient,
    unitaryMatrixDualCasimirHeatCoefficientReal_trivialClass bridge]
  norm_num

variable [CompactSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Conditional normalized-Haar mass one for the positive-time candidate spectral series. The proof
is exact trivial-character coefficient recovery, not a positivity argument. -/
theorem normalizedCompactHaar_integral_casimirHeatCharacterSeries
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    (∫ g, unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g
      ∂normalizedCompactHaarMeasure G) = 1 := by
  have h := normalizedCompactHaar_characterAnalysis_casimirHeatCharacterSeries
    heatTraceData ht (unitaryMatrixDualTrivialClass G)
  simp only [unitaryMatrixDualCharacter_trivialClass, star_one, one_mul] at h
  rw [h, unitaryMatrixDualCasimirHeatCoefficient_trivialClass bridge]

end

end Mathematics
end YangMills
