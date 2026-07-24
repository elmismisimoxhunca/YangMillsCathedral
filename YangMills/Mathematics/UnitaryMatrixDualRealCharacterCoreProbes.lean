/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualRealCharacterCore

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
  {inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)}
  (realLaplacian : RightInvariantPairingLaplacianData inner)
  (complexLaplacian : RightInvariantPairingComplexLaplacianData inner)
  {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
  (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
    inner complexLaplacian heatTraceData)

/-- Exact pointwise real and imaginary component probe. -/
theorem exact_realCharacter_components
    (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q .real g =
        (unitaryMatrixDualCharacter q g).re ∧
      unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q .imaginary g =
        (unitaryMatrixDualCharacter q g).im := by
  simp

/-- Exact real pairing-Laplacian eigenvalue probe for either component. -/
theorem exact_realCharacterComponent_laplacian
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent)
    (g : G) :
    realLaplacian.laplacian
      (unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component) g =
      -(heatTraceData.casimirWeight q) *
        unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component g :=
  laplacian_unitaryMatrixDualSmoothRealCharacterComponent
    realLaplacian complexLaplacian casimirBridge q component g

/-- Exact probe: finite real synthesis is an algebraic linear map. -/
theorem exact_realCharacterSynthesis_linearity
    (c : ℝ) (a b : UnitaryMatrixDualRealCharacterCoefficients G) :
    unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge (c • a + b) =
      c • unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge a +
        unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge b := by
  rw [map_add, map_smul]

/-- Every individual real or imaginary component belongs to the designated finite synthesis range. -/
theorem exact_realCharacterComponent_mem_core
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent) :
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component ∈
      unitaryMatrixDualSmoothRealCharacterCore casimirBridge :=
  unitaryMatrixDualSmoothRealCharacterComponent_mem_core casimirBridge q component

/-- Exact scope probe: every member of this character range is central. -/
theorem exact_realCharacterCore_central
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ unitaryMatrixDualSmoothRealCharacterCore casimirBridge)
    (g h : G) : f (h * g * h⁻¹) = f g :=
  unitaryMatrixDualSmoothRealCharacterCore_conj casimirBridge hf g h

/-- Hostile scope probe: a noncentral smooth test cannot be smuggled into the character range. -/
theorem noncentral_not_in_realCharacterCore
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hnot : ∃ g h : G, f (h * g * h⁻¹) ≠ f g) :
    f ∉ unitaryMatrixDualSmoothRealCharacterCore casimirBridge :=
  not_mem_unitaryMatrixDualSmoothRealCharacterCore_of_not_central
    casimirBridge f hnot

/-- Hostile eigenvalue probe: changing a component's real Laplacian value is contradictory. -/
theorem changed_realCharacterComponent_laplacian_blocked
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent)
    (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      -(heatTraceData.casimirWeight q) *
        unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component g)
    (claimed : realLaplacian.laplacian
      (unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component) g = changed) :
    False := by
  apply changed_ne_exact
  rw [← claimed]
  exact laplacian_unitaryMatrixDualSmoothRealCharacterComponent
    realLaplacian complexLaplacian casimirBridge q component g

end

end Mathematics
end YangMills
