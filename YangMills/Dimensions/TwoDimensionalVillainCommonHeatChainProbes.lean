/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalVillainCommonHeatChain

namespace YangMills.Dimensions.TwoDimensionalVillainCommonHeatChain.Probes

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
    {Connection : Type uConnection} {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}

/-- Driver 8.5 requires the exact identity derivative to be injective, without global faithfulness. -/
theorem exact_differential_injective
    (data : TwoDimensionalVillainCommonHeatChainData (gaugeGroup := gaugeGroup) semigroup) :
    Function.Injective data.representation.differential :=
  data.representation.differential_injective_exact

/-- The Laplacian pairing is induced by that same representation differential. -/
theorem exact_common_pairing
    (data : TwoDimensionalVillainCommonHeatChainData (gaugeGroup := gaugeGroup) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    data.inner.pairing first second =
      twoDimensionalRepresentationTracePairing data.representation first second :=
  data.inner_pairing_eq_trace semigroup first second

/-- The heat equation retains the unchanged selected density family. -/
theorem exact_selected_density
    (data : TwoDimensionalVillainCommonHeatChainData (gaugeGroup := gaugeGroup) semigroup)
    (time : ℝ) (positive : 0 < time) (g : G) :
    ENNReal.ofReal (data.heat.densityReal time g) = law.selectedAreaDensity time g :=
  data.heat.densityReal_toENNReal time positive g

/-- A noninjective exact derivative is hostilely rejected. -/
theorem noninjective_differential_blocked
    (data : TwoDimensionalVillainCommonHeatChainData (gaugeGroup := gaugeGroup) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
    (different : first ≠ second)
    (same : data.representation.differential first = data.representation.differential second) :
    False :=
  different (data.representation.differential_injective_exact same)

/-- An unrelated pairing cannot be substituted into the Villain heat chain. -/
theorem unrelated_pairing_blocked
    (data : TwoDimensionalVillainCommonHeatChainData (gaugeGroup := gaugeGroup) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
    (claimed : data.inner.pairing first second ≠
      twoDimensionalRepresentationTracePairing data.representation first second) : False :=
  claimed (data.inner_pairing_eq_trace semigroup first second)

end

end YangMills.Dimensions.TwoDimensionalVillainCommonHeatChain.Probes
