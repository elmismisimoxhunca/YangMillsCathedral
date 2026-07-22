/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalWilsonCommonHeatChain

/-!
# Probes for the common Wilson/continuum heat chain
-/

namespace YangMills.Dimensions.TwoDimensionalWilsonCommonHeatChain.Probes

open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The source's connected compact Lie-group hypothesis is explicit in the common chain. -/
theorem exact_connected_group
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup) :
    IsConnected (Set.univ : Set G) :=
  data.group_connected

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Every Wilson action uses the same smooth representation whose derivative drives the heat chain. -/
theorem exact_wilson_representation
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup)
    (spacing : PositiveLatticeSpacing) (g : G) :
    (data.wilsonFamily semigroup |>.actionAt spacing).action g =
      (data.normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (data.representation.representation g)).re) :=
  data.actionAt_formula semigroup spacing g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The same representation is both globally faithful and infinitesimally injective. -/
theorem exact_two_faithfulness_hypotheses
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup) :
    Function.Injective data.representation.representation ∧
      Function.Injective data.representation.differential :=
  ⟨data.representation_faithful,
    data.representation.differential_injective_exact⟩

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The Laplacian's invariant pairing is exactly the same representation trace pairing. -/
theorem exact_common_pairing
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    data.inner.pairing first second =
      twoDimensionalRepresentationTracePairing data.representation first second :=
  data.inner_pairing_eq_trace semigroup first second

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Substituting an unrelated pairing into the common heat chain is hostilely rejected. -/
theorem unrelated_heat_pairing_blocked
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
    (claimed : data.inner.pairing first second ≠
      twoDimensionalRepresentationTracePairing data.representation first second) : False :=
  claimed (data.inner_pairing_eq_trace semigroup first second)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Substituting an unfaithful global representation is hostilely rejected. -/
theorem unfaithful_wilson_pair_blocked
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup)
    (first second : G) (different : first ≠ second)
    (same : data.representation.representation first =
      data.representation.representation second) : False :=
  different (data.representation_faithful same)

end

end YangMills.Dimensions.TwoDimensionalWilsonCommonHeatChain.Probes
