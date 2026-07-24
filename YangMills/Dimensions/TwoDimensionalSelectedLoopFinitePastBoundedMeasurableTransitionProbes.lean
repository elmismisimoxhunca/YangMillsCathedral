/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastBoundedMeasurableTransition

/-!
# Hostile probes for bounded-measurable finite process histories
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
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))

omit [FiniteDimensional ℝ E] in
/-- Exact generic identity for a bounded measurable increment-history test and arbitrary continuous
state extracted from that history. -/
theorem exact_finitePastIncrement_boundedMeasurable_weakMarkov_identity
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Φ : (Fin n → G) → ℝ) (Φ_measurable : Measurable Φ)
    (bound : ℝ) (Φ_bound : ∀ history, ‖Φ history‖ ≤ bound)
    (state : C(Fin n → G, G)) (f : C(G, ℝ)) :
    (∫ samplePoint,
      Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
        f (state (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
          twoDimensionalFinalRightIncrement bridge.brownian n times samplePoint)
      ∂bridge.brownian.probabilityMeasure) =
    ∫ samplePoint,
      Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (state (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint))
      ∂bridge.brownian.probabilityMeasure :=
  bridge.finitePastIncrement_boundedMeasurable_weakMarkov_identity
    n times times_monotone t ht final_time Φ Φ_measurable bound Φ_bound state f

omit [FiniteDimensional ℝ E] in
/-- Hostile generic-state probe: changing the transition attached to an arbitrary continuous state
extractor contradicts the generic bounded-measurable identity. -/
theorem changed_genericState_boundedMeasurable_transition_blocked
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Φ : (Fin n → G) → ℝ) (Φ_measurable : Measurable Φ)
    (bound : ℝ) (Φ_bound : ∀ history, ‖Φ history‖ ≤ bound)
    (state : C(Fin n → G, G)) (f : C(G, ℝ)) (changed : ℝ)
    (changed_ne_exact : changed ≠
      ∫ samplePoint,
        Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
          bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
            (state (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint))
        ∂bridge.brownian.probabilityMeasure)
    (claimed :
      (∫ samplePoint,
        Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
          f (state (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
            twoDimensionalFinalRightIncrement bridge.brownian n times samplePoint)
        ∂bridge.brownian.probabilityMeasure) = changed) : False := by
  rw [bridge.finitePastIncrement_boundedMeasurable_weakMarkov_identity
    n times times_monotone t ht final_time Φ Φ_measurable bound Φ_bound state f] at claimed
  exact changed_ne_exact claimed.symm

omit [FiniteDimensional ℝ E] in
/-- Exact identity for arbitrary bounded measurable tests of actual finite process histories. -/
theorem exact_finiteProcessHistory_boundedMeasurable_weakMarkov_identity
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (times_zero : times 0 = 0) (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Ψ : (Fin n → G) → ℝ) (Ψ_measurable : Measurable Ψ)
    (bound : ℝ) (Ψ_bound : ∀ history, ‖Ψ history‖ ≤ bound) (f : C(G, ℝ)) :
    (∫ samplePoint,
      Ψ (twoDimensionalPastProcessValues bridge.brownian n times samplePoint) *
        f (bridge.brownian.process (times (Fin.last (n + 1))) samplePoint)
      ∂bridge.brownian.probabilityMeasure) =
    ∫ samplePoint,
      Ψ (twoDimensionalPastProcessValues bridge.brownian n times samplePoint) *
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (bridge.brownian.process (times (Fin.last n).castSucc) samplePoint)
      ∂bridge.brownian.probabilityMeasure :=
  bridge.finiteProcessHistory_boundedMeasurable_weakMarkov_identity
    n times times_monotone times_zero t ht final_time
      Ψ Ψ_measurable bound Ψ_bound f

omit [FiniteDimensional ℝ E] in
/-- Hostile bounded-measurable probe: changing the exact transition value is contradictory. -/
theorem changed_boundedMeasurable_processHistory_transition_blocked
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (times_zero : times 0 = 0) (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Ψ : (Fin n → G) → ℝ) (Ψ_measurable : Measurable Ψ)
    (bound : ℝ) (Ψ_bound : ∀ history, ‖Ψ history‖ ≤ bound) (f : C(G, ℝ))
    (changed : ℝ)
    (changed_ne_exact : changed ≠
      ∫ samplePoint,
        Ψ (twoDimensionalPastProcessValues bridge.brownian n times samplePoint) *
          bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
            (bridge.brownian.process (times (Fin.last n).castSucc) samplePoint)
        ∂bridge.brownian.probabilityMeasure)
    (claimed :
      (∫ samplePoint,
        Ψ (twoDimensionalPastProcessValues bridge.brownian n times samplePoint) *
          f (bridge.brownian.process (times (Fin.last (n + 1))) samplePoint)
        ∂bridge.brownian.probabilityMeasure) = changed) : False := by
  rw [bridge.finiteProcessHistory_boundedMeasurable_weakMarkov_identity
    n times times_monotone times_zero t ht final_time
      Ψ Ψ_measurable bound Ψ_bound f] at claimed
  exact changed_ne_exact claimed.symm

end

end YangMills.Dimensions
