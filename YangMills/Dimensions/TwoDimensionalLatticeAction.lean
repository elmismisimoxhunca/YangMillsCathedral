/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalVillainAction
import YangMills.Dimensions.TwoDimensionalWilsonAction

/-!
# Driver two-dimensional lattice action contract

Driver Definition 7.1 requires a continuous, strictly positive, normalized class function invariant
under inversion. This module packages that exact common contract and constructs it from the already
source-qualified Villain and Wilson chains without identifying those two action families.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

/-- Driver Definition 7.1 action function at one fixed lattice spacing. -/
structure TwoDimensionalLatticeActionData
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] where
  action : G → ℝ
  action_continuous : Continuous action
  action_pos : ∀ g, 0 < action g
  action_central : ∀ h g, action (h * g * h⁻¹) = action g
  action_inv : ∀ g, action g⁻¹ = action g
  action_integral_normalized :
    ∫ g, action g ∂normalizedCompactHaarMeasure G = 1

namespace TwoDimensionalLatticeActionData

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Driver's contract rules out the zero action. -/
theorem action_ne_zero (data : TwoDimensionalLatticeActionData G) : data.action ≠ 0 := by
  intro hzero
  have hpos := data.action_pos 1
  rw [hzero] at hpos
  simp at hpos

/-- The Villain heat-kernel chain supplies the common action contract at each positive spacing. -/
def villain
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    (heat : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian)
    (kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) : TwoDimensionalLatticeActionData G where
  action := twoDimensionalVillainAction heat kernel spacing
  action_continuous := TwoDimensionalVillainAction.action_continuous heat kernel spacing
  action_pos := TwoDimensionalVillainAction.action_pos heat kernel spacing
  action_central := TwoDimensionalVillainAction.action_central heat kernel spacing
  action_inv := TwoDimensionalVillainAction.action_inv heat kernel spacing
  action_integral_normalized :=
    TwoDimensionalVillainAction.action_integral_normalized heat kernel spacing

/-- The exact unitary-character Wilson chain supplies the same common action contract. -/
def wilson
    {representation : FiniteDimensionalUnitaryRepresentationCharacterData G}
    (normalization : TwoDimensionalWilsonNormalizerData representation)
    (spacing : PositiveLatticeSpacing) : TwoDimensionalLatticeActionData G where
  action := twoDimensionalWilsonAction normalization spacing
  action_continuous := TwoDimensionalWilsonAction.action_continuous normalization spacing
  action_pos := TwoDimensionalWilsonAction.action_pos normalization spacing
  action_central := TwoDimensionalWilsonAction.action_central normalization spacing
  action_inv := TwoDimensionalWilsonAction.action_inv normalization spacing
  action_integral_normalized :=
    TwoDimensionalWilsonAction.action_integral_normalized normalization spacing

/-- The constant normalized action is an elementary positive inhabitant of Definition 7.1. It is
not a Villain action, Wilson action, lattice field measure, or convergence witness. -/
def constantOne : TwoDimensionalLatticeActionData G where
  action := fun _ => 1
  action_continuous := continuous_const
  action_pos := fun _ => zero_lt_one
  action_central := fun _ _ => rfl
  action_inv := fun _ => rfl
  action_integral_normalized := by
    letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
      normalizedCompactHaarMeasure_isProbability G
    simp

end TwoDimensionalLatticeActionData

end

end YangMills.Dimensions
