/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily

/-!
# Probes for source-coherent spacing-indexed actions
-/

namespace YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily.Probes

open Filter MeasureTheory Set
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection

/-- The designated right-neighborhood filter is genuinely nontrivial. -/
theorem spacing_filter_neBot : NeBot positiveLatticeSpacingAtZero :=
  inferInstance

/-- The exact positive spacing coercion tends to real zero from the right. -/
theorem spacing_tends_to_zero_from_right :
    Tendsto (fun spacing : PositiveLatticeSpacing => spacing.1)
      positiveLatticeSpacingAtZero (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
  positiveLatticeSpacingAtZero_tendsto

/-- Constant quantities converge to their exact value as spacing tends to zero. -/
theorem constant_tends_to_at_zero (value : ℝ) :
    TwoDimensionalTendsToAtZero (fun _ => value) value :=
  tendsto_const_nhds

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Driver faithfulness recovers group elements through the exact representation used by the family. -/
theorem faithful_representation_recovers_group_elements
    (data : FaithfulWilsonActionFamilyData (G := G))
    {first second : G}
    (equality : data.representationData.representation first =
      data.representationData.representation second) : first = second :=
  data.representation_faithful equality

/-- The Wilson family retains the same faithful trace representation at every spacing. -/
theorem exact_wilson_family_formula
    (data : FaithfulWilsonActionFamilyData (G := G))
    (spacing : PositiveLatticeSpacing) (g : G) :
    (data.actionAt spacing).action g =
      (data.normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (data.representationData.representation g)).re) :=
  data.actionAt_formula spacing g

/-- The Villain family retains the unchanged heat density `Q_{ε²}` at every spacing. -/
theorem exact_villain_family_formula
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
    (spacing : PositiveLatticeSpacing) (g : G) :
    (twoDimensionalVillainActionFamily heat kernel spacing).action g =
      heat.densityReal (spacing.1 ^ 2) g :=
  rfl

/-- A claimed collapse under the representation used by the Wilson family is rejected. -/
theorem unfaithful_pair_blocked
    (data : FaithfulWilsonActionFamilyData (G := G))
    (first second : G) (different : first ≠ second)
    (sameMatrix : data.representationData.representation first =
      data.representationData.representation second) : False :=
  different (data.representation_faithful sameMatrix)

end

end YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily.Probes
