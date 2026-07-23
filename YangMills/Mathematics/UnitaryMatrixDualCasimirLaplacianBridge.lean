/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantComplexLaplacian
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatDerivativeSeries

/-!
# Bridge from candidate Casimir weights to the pairing-normalized geometric Laplacian

The existing heat-trace data stores only nonnegative candidate weights `c_q`; it does not identify
them with the geometric operator. This file makes the missing identification an explicit,
uninhabited bridge. For the exact complex right-invariant Laplacian determined by one invariant
pairing, every selected character must be smooth and satisfy

`Δ χ_q = -c_q χ_q`.

The sign is Driver's convention `∂ₜ = 1/2 Δ`, and it matches the existing coefficient
`dim(q) exp (-(t/2)c_q)`. The file proves that the eigenvalue is unique because
`χ_q(1)=dim(q)>0`, proves the exact derivative of the candidate coefficient, and derives the
single-character term identity underlying the heat equation.

No bridge inhabitant is constructed. No infinite series is differentiated, no Laplacian is passed
through a `tsum`, and no heat equation, positivity, normalization, or heat-kernel theorem for the
summed spectral family is claimed.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Explicit unresolved identification of every candidate Casimir weight with the eigenvalue of the
pairing-normalized complex right-invariant Laplacian on the matching selected character. -/
structure UnitaryMatrixDualCasimirLaplacianBridgeData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    (laplacianData : RightInvariantPairingComplexLaplacianData inner)
    (heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) where
  character_contMDiff : ∀ q : UnitaryMatrixDual G,
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) ∞
      (unitaryMatrixDualCharacter q)
  character_laplacian : ∀ (q : UnitaryMatrixDual G) (g : G),
    laplacianData.laplacian
      { toFun := unitaryMatrixDualCharacter q
        contMDiff := character_contMDiff q } g =
      -(heatTraceData.casimirWeight q : ℂ) * unitaryMatrixDualCharacter q g

namespace UnitaryMatrixDualCasimirLaplacianBridgeData

/-- The selected character packaged as a smooth complex scalar function using the bridge's explicit
smoothness field. -/
def smoothCharacter
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) : SmoothLieGroupComplexFunction (E := E) (G := G) :=
  ⟨unitaryMatrixDualCharacter q, bridge.character_contMDiff q⟩

@[simp]
theorem smoothCharacter_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (g : G) :
    bridge.smoothCharacter q g = unitaryMatrixDualCharacter q g :=
  rfl

/-- Restatement of the exact signed character eigenvalue equation on the packaged smooth
character. -/
theorem laplacian_smoothCharacter
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (g : G) :
    laplacianData.laplacian (bridge.smoothCharacter q) g =
      -(heatTraceData.casimirWeight q : ℂ) * unitaryMatrixDualCharacter q g := by
  exact bridge.character_laplacian q g

/-- The real eigenvalue attached to a selected character is unique for the fixed Laplacian. The
proof evaluates at the identity and uses the strictly positive representation dimension. -/
theorem casimirWeight_eq_of_character_laplacian
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (q : UnitaryMatrixDual G) (candidate : ℝ)
    (candidateEquation : ∀ g : G,
      laplacianData.laplacian (bridge.smoothCharacter q) g =
        -(candidate : ℂ) * unitaryMatrixDualCharacter q g) :
    candidate = heatTraceData.casimirWeight q := by
  have heq := (candidateEquation (1 : G)).symm.trans
    (bridge.laplacian_smoothCharacter q 1)
  rw [unitaryMatrixDualCharacter_one] at heq
  have hd : (unitaryMatrixDualDimension q : ℂ) ≠ 0 := by
    exact_mod_cast (unitaryMatrixDualRepresentative q).dimension_pos.ne'
  have hn := mul_right_cancel₀ hd heq
  have hc : (candidate : ℂ) = (heatTraceData.casimirWeight q : ℂ) := by
    exact neg_inj.mp hn
  exact_mod_cast hc

end UnitaryMatrixDualCasimirLaplacianBridgeData

/-- Exact single-character spectral identity behind Driver's `∂ₜ = 1/2 Δ` convention. The left
factor is the derivative of the real coefficient proved in the imported derivative-series module;
this theorem does not
exchange the Laplacian or time derivative with an infinite sum. -/
theorem unitaryMatrixDualCasimirHeatTerm_derivative_eq_half_laplacian
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (t : ℝ) (q : UnitaryMatrixDual G) (g : G) :
    (unitaryMatrixDualCasimirHeatDerivativeCoefficientReal heatTraceData t q : ℂ) *
        unitaryMatrixDualCharacter q g =
      (1 / 2 : ℂ) *
        (unitaryMatrixDualCasimirHeatCoefficientReal heatTraceData t q : ℂ) *
        laplacianData.laplacian (bridge.smoothCharacter q) g := by
  rw [bridge.laplacian_smoothCharacter]
  unfold unitaryMatrixDualCasimirHeatDerivativeCoefficientReal
  push_cast
  ring

end

end Mathematics
end YangMills
