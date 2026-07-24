/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralHeatOperatorLinear

namespace YangMills
namespace Dimensions

open Filter MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff Topology

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact positive-time linearity probe. -/
theorem exact_positiveHeatOperator_linearity
    (t : ℝ) (ht : 0 < t) (c : ℝ) (f h : C(G, ℝ)) :
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht (c • f + h) =
      c • twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f +
        twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht h := by
  rw [map_add, map_smul]

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact probability-measure contraction probe. -/
theorem exact_positiveHeatOperator_norm_le
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) :
    ‖twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f‖ ≤ ‖f‖ :=
  twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_norm_le bridge t ht f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact positive-time Markov-operator probe: constants, positivity, and order are preserved. -/
theorem exact_positiveHeatOperator_markov
    (t : ℝ) (ht : 0 < t) (c : ℝ) (f h : C(G, ℝ))
    (hf : ∀ g, 0 ≤ f g) (hfh : ∀ g, f g ≤ h g) :
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht
        (ContinuousMap.const G c) = ContinuousMap.const G c ∧
      (∀ g, 0 ≤ twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f g) ∧
      (∀ g, twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f g ≤
        twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht h g) :=
  ⟨twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_const bridge t ht c,
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_nonneg bridge t ht f hf,
    twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_mono bridge t ht f h hfh⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile constant-preservation probe: a changed constant output is contradictory. -/
theorem changed_positiveHeatOperator_const_blocked
    (t : ℝ) (ht : 0 < t) (c : ℝ) (changed : C(G, ℝ))
    (changed_ne_const : changed ≠ ContinuousMap.const G c)
    (claimed : twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht
      (ContinuousMap.const G c) = changed) : False :=
  changed_ne_const (claimed.symm.trans
    (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_const bridge t ht c))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile positivity probe: nonnegative input cannot acquire a negative value. -/
theorem negative_positiveHeatOperator_output_blocked
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (hf : ∀ g, 0 ≤ f g) (g : G)
    (claimed : twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f g < 0) :
    False :=
  (not_lt_of_ge
    (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_nonneg bridge t ht f hf g)) claimed

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact continuous-linear realization and operator-norm probe. -/
theorem exact_positiveHeatOperator_continuousLinearMap
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) :
    twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap bridge t ht f =
      bridge.spectralHeatKernel.kernelOperator.heatOperator t f ∧
    ‖twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap bridge t ht‖ ≤ 1 :=
  ⟨twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap_apply bridge t ht f,
    twoDimensionalSelectedLoopPositiveHeatOperatorContinuousLinearMap_norm_le_one bridge t ht⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact total nonnegative-time contraction-semigroup probe. -/
theorem exact_heatOperatorContinuousLinearMap_semigroup
    (s t : NNReal) (f : C(G, ℝ)) :
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f =
      bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f ∧
    ‖twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t‖ ≤ 1 ∧
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge (s + t) =
      (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge s).comp
        (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t) :=
  ⟨twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_apply bridge t f,
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_norm_le_one bridge t,
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_add bridge s t⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact zero-time branch of the total continuous-linear heat family. -/
theorem exact_heatOperatorContinuousLinearMap_zero :
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge 0 =
      ContinuousLinearMap.id ℝ C(G, ℝ) := by
  unfold twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap
  rw [dif_neg (lt_irrefl 0)]

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact Markov-order properties of the total nonnegative-time family. -/
theorem exact_heatOperatorContinuousLinearMap_markov
    (t : NNReal) (c : ℝ) (f h : C(G, ℝ))
    (hf : ∀ g, 0 ≤ f g) (hfh : ∀ g, f g ≤ h g) :
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t
        (ContinuousMap.const G c) = ContinuousMap.const G c ∧
      (∀ g, 0 ≤ twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f g) ∧
      (∀ g, twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f g ≤
        twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t h g) :=
  ⟨twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_const bridge t c,
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_nonneg bridge t f hf,
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_mono bridge t f h hfh⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile contraction probe: a strict uniform-norm increase is contradictory. -/
theorem expanded_positiveHeatOperator_norm_blocked
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ))
    (claimed : ‖f‖ < ‖twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f‖) :
    False :=
  (not_lt_of_ge
    (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_norm_le bridge t ht f)) claimed

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact algebraic recovery of the total heat operator from the totalized quotient. -/
theorem exact_heatOperator_eq_add_smul_differenceQuotient
    (t : NNReal) (f : C(G, ℝ)) :
    twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t f =
      f + (t : ℝ) • twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f :=
  twoDimensionalSelectedLoopHeatOperator_eq_add_smul_differenceQuotient bridge t f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact contraction-derived quotient bound with its singular inverse-time factor exposed. -/
theorem exact_heatDifferenceQuotientLinearMap_norm_le
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) :
    ‖twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f‖ ≤
      2 * (t : ℝ)⁻¹ * ‖f‖ :=
  twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_norm_le bridge t ht f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact totalization probe: the excluded zero-time branch is the zero linear map. -/
theorem exact_heatDifferenceQuotientLinearMap_zero :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge 0 = 0 :=
  twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_zero bridge

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile zero-branch probe: no changed linear map can replace the designated totalization. -/
theorem changed_heatDifferenceQuotientLinearMap_zero_blocked
    (changed : C(G, ℝ) →ₗ[ℝ] C(G, ℝ)) (changed_ne_zero : changed ≠ 0)
    (claimed : twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge 0 = changed) :
    False :=
  changed_ne_zero (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_zero bridge))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact pointwise quotient probe. -/
theorem exact_heatDifferenceQuotientLinearMap
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f g =
      (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g - f g) /
        (t : ℝ) :=
  twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply_point bridge t ht f g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile total-semigroup probe: changing the composed operator is contradictory. -/
theorem changed_heatOperatorContinuousLinearMap_semigroup_blocked
    (s t : NNReal) (changed : C(G, ℝ) →L[ℝ] C(G, ℝ))
    (changed_ne_exact : changed ≠
      (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge s).comp
        (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge t))
    (claimed : twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap bridge (s + t) =
      changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatOperatorContinuousLinearMap_add bridge s t))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile probe: the positive heat linear map cannot be changed while preserving its designated
operator value. -/
theorem changed_positiveHeatOperatorLinearMap_blocked
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      bridge.spectralHeatKernel.kernelOperator.heatOperator t f)
    (claimed : twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap bridge t ht f = changed) :
    False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopPositiveHeatOperatorLinearMap_apply bridge t ht f))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile quotient probe: a changed scalar point value contradicts the exact bundled quotient. -/
theorem changed_heatDifferenceQuotientLinearMap_point_blocked
    (t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      (bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g - f g) / (t : ℝ))
    (claimed : twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap bridge t f g = changed) :
    False :=
  changed_ne_exact (claimed.symm.trans
    (twoDimensionalSelectedLoopHeatDifferenceQuotientLinearMap_apply_point bridge t ht f g))

end

end Dimensions
end YangMills
