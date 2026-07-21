/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeAction

/-!
# Source-coherent two-dimensional lattice action families

Driver §8 varies one exact action with every positive lattice spacing and then sends the spacing to
zero. Rather than expose an arbitrary family record, this module provides only exact Villain and
Wilson constructors. The Wilson family bundles faithfulness and normalization with the same matrix
representation used by every action.
-/

namespace YangMills.Dimensions

open Filter MeasureTheory Set
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection

/-- The punctured right-neighborhood filter `ε → 0⁺` on exact positive lattice spacings. -/
def positiveLatticeSpacingAtZero : Filter PositiveLatticeSpacing :=
  Filter.comap Subtype.val (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The positive-spacing filter is nontrivial. -/
instance positiveLatticeSpacingAtZero_neBot : NeBot positiveLatticeSpacingAtZero := by
  apply Filter.comap_neBot
  intro set setMembership
  have intersectionMembership : set ∩ Set.Ioi (0 : ℝ) ∈
      nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    inter_mem setMembership self_mem_nhdsWithin
  obtain ⟨value, valueSet, valuePositive⟩ :=
    Filter.nonempty_of_mem intersectionMembership
  exact ⟨⟨value, valuePositive⟩, valueSet⟩

/-- The spacing coercion genuinely tends to real zero along the designated filter. -/
theorem positiveLatticeSpacingAtZero_tendsto :
    Tendsto (fun spacing : PositiveLatticeSpacing => spacing.1)
      positiveLatticeSpacingAtZero (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
  Filter.tendsto_comap

/-- Convergence of spacing-indexed real quantities as `ε → 0⁺`. -/
def TwoDimensionalTendsToAtZero
    (quantity : PositiveLatticeSpacing → ℝ) (limit : ℝ) : Prop :=
  Tendsto quantity positiveLatticeSpacingAtZero (nhds limit)

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The unchanged heat-kernel chain gives the exact Villain family `Aᵋ = Q_{ε²}`. -/
def twoDimensionalVillainActionFamily
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
    (kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat) :
    PositiveLatticeSpacing → TwoDimensionalLatticeActionData G :=
  TwoDimensionalLatticeActionData.villain heat kernel

/-- The Wilson action-family hypotheses used by Theorem 8.10: normalization and actual
faithfulness refer to the same representation used by every spacing-indexed action. This supplies no
graph, approximating sequence, observable transport, measure limit, or convergence theorem. -/
structure FaithfulWilsonActionFamilyData where
  representationData : FiniteDimensionalUnitaryRepresentationCharacterData G
  normalization : TwoDimensionalWilsonNormalizerData representationData
  representation_faithful : Function.Injective representationData.representation

namespace FaithfulWilsonActionFamilyData

/-- The exact Wilson Definition 7.1 action at each spacing. -/
def actionAt (data : FaithfulWilsonActionFamilyData (G := G))
    (spacing : PositiveLatticeSpacing) : TwoDimensionalLatticeActionData G :=
  TwoDimensionalLatticeActionData.wilson data.normalization spacing

/-- The action family and faithfulness field use literally the same representation. -/
theorem actionAt_formula (data : FaithfulWilsonActionFamilyData (G := G))
    (spacing : PositiveLatticeSpacing) (g : G) :
    (data.actionAt spacing).action g =
      (data.normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (data.representationData.representation g)).re) :=
  rfl

end FaithfulWilsonActionFamilyData

/-- At every spacing, the Villain family is definitionally the exact `Q_{ε²}` action contract. -/
theorem twoDimensionalVillainActionFamily_actionAt
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
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalVillainActionFamily heat kernel spacing =
      TwoDimensionalLatticeActionData.villain heat kernel spacing :=
  rfl

end

end YangMills.Dimensions
