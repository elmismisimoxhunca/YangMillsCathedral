/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastSpectralTransition

/-!
# Hostile probes for finite-past spectral transition
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
/-- Exact positive probe for every finite history length and every continuous extracted state. -/
theorem exact_finitePastIncrement_weakMarkov_identity
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Φ : C(Fin n → G, ℝ)) (state : C(Fin n → G, G)) (f : C(G, ℝ)) :
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
  bridge.finitePastIncrement_weakMarkov_identity
    n times times_monotone t ht final_time Φ state f

omit [FiniteDimensional ℝ E] in
/-- Hostile operator probe: changing the right-hand transition value contradicts the exact
finite-history identity. -/
theorem changed_finitePast_transition_blocked
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Φ : C(Fin n → G, ℝ)) (state : C(Fin n → G, G)) (f : C(G, ℝ))
    (changed : ℝ)
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
  rw [bridge.finitePastIncrement_weakMarkov_identity
    n times times_monotone t ht final_time Φ state f] at claimed
  exact changed_ne_exact claimed.symm

end

end YangMills.Dimensions
