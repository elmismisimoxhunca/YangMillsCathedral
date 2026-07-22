/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalRepresentationInducedPairing
import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator

/-!
# Common representation/heat chain for Driver's Villain theorem

Driver Theorem 8.5 assumes injectivity of the exact representation differential `p_*`, not global
faithfulness of the group representation and not Wilson normalization. This record retains exactly
that distinction while tying the same differential-induced pairing to the Laplacian, selected heat
density, and kernel. The record now has Driver's connected compact Lie-group scope: connectedness is
explicit, while compact simplicity is deliberately absent.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge] {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)

/-- Driver 8.5's exact differential-induced Villain heat chain, without Wilson assumptions. -/
structure TwoDimensionalVillainCommonHeatChainCoreData where
  group_connected : IsConnected (Set.univ : Set G)
  representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)
  inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)
  pairing_coherence :
    TwoDimensionalRepresentationInducedPairingCoherenceData representation inner
  laplacian : RightInvariantPairingLaplacianData inner
  heat : TwoDimensionalSelectedLoopHeatEquationCoreData
    inner law semigroup laplacian
  kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat

set_option linter.unusedVariables false
/-- Compatibility alias for the former compact-simple-indexed surface. The index is phantom; the
underlying theorem data has connected compact Lie-group scope. This is type-only compatibility;
declarations live in the core namespace. -/
abbrev TwoDimensionalVillainCommonHeatChainData
    (gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E)
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law) :=
  TwoDimensionalVillainCommonHeatChainCoreData (E := E) semigroup
set_option linter.unusedVariables true

namespace TwoDimensionalVillainCommonHeatChainCoreData

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The invariant pairing is literally induced by the same representation whose exact derivative is
injective. -/
theorem inner_pairing_eq_trace
    (data : TwoDimensionalVillainCommonHeatChainCoreData (E := E) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    data.inner.pairing first second =
      twoDimensionalRepresentationTracePairing data.representation first second :=
  data.pairing_coherence.pairing_eq_trace first second

end TwoDimensionalVillainCommonHeatChainCoreData

end

end YangMills.Dimensions
