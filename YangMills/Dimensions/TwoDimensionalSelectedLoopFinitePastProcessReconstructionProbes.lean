/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastProcessReconstruction

/-!
# Hostile probes for finite-past process reconstruction
-/

namespace YangMills.Dimensions

open MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    {heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian}
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)

omit [T2Space G] [SecondCountableTopology G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The history-product state is genuinely packaged as a continuous map. -/
theorem exact_historyProduct_continuous (n : ℕ) :
    Continuous (finiteRightIncrementHistoryProduct (G := G) n) :=
  (finiteRightIncrementHistoryProduct n).continuous

omit [T2Space G] [SecondCountableTopology G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every prefix-product coordinate is packaged in one continuous history-to-process-vector map. -/
theorem exact_prefixProducts_continuous (n : ℕ) :
    Continuous (finiteRightIncrementPrefixProductsContinuousMap (G := G) n) :=
  (finiteRightIncrementPrefixProductsContinuousMap n).continuous

omit [T2Space G] [SecondCountableTopology G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Empty increment history has the exact identity product. -/
theorem empty_historyProduct_exact (history : Fin 0 → G) :
    finiteRightIncrementHistoryProduct 0 history = 1 := by
  simp [finiteRightIncrementHistoryProduct]

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Endpoint probe before using the almost-sure identity start. -/
theorem exact_historyProduct_endpoints
    (n : ℕ) (times : Fin (n + 2) → NNReal) (samplePoint : Ω) :
    twoDimensionalPastRightIncrementProduct brownian n times samplePoint =
      (brownian.process (times 0) samplePoint)⁻¹ *
        brownian.process (times (Fin.last n).castSucc) samplePoint :=
  brownian.pastRightIncrementProduct_eq_endpoints n times samplePoint

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact almost-sure reconstruction at the final history time. -/
theorem exact_historyProduct_currentState
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_zero : times 0 = 0) :
    ∀ᵐ samplePoint ∂brownian.probabilityMeasure,
      twoDimensionalPastRightIncrementProduct brownian n times samplePoint =
        brownian.process (times (Fin.last n).castSucc) samplePoint :=
  brownian.pastRightIncrementProduct_ae_eq_currentState n times times_zero

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The complete prefix-product vector simultaneously reconstructs all selected past process
values. -/
theorem exact_prefixProducts_processValues
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_zero : times 0 = 0) :
    ∀ᵐ samplePoint ∂brownian.probabilityMeasure,
      finiteRightIncrementPrefixProductsContinuousMap n
          (twoDimensionalPastRightIncrements brownian n times samplePoint) =
        twoDimensionalPastProcessValues brownian n times samplePoint :=
  brownian.pastRightIncrementPrefixProducts_ae_eq_processValues n times times_zero

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile endpoint probe: a distinct proposed endpoint cannot equal the exact history product. -/
theorem changed_historyProduct_endpoint_blocked
    (n : ℕ) (times : Fin (n + 2) → NNReal) (samplePoint : Ω) (changed : G)
    (changed_ne_exact : changed ≠
      (brownian.process (times 0) samplePoint)⁻¹ *
        brownian.process (times (Fin.last n).castSucc) samplePoint)
    (claimed : twoDimensionalPastRightIncrementProduct brownian n times samplePoint = changed) :
    False := by
  rw [brownian.pastRightIncrementProduct_eq_endpoints] at claimed
  exact changed_ne_exact claimed.symm

end

end YangMills.Dimensions
