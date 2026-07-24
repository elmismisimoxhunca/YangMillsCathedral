/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastProcessReconstruction
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastSpectralTransition

/-!
# Finite increment-history transition for actual process states

The finite-history spectral transition identity initially uses an arbitrary continuous state
extracted from the increment vector. The ordered increment product and identity start reconstruct the
actual current process state almost surely. This module therefore rewrites both sides into an exact
weak transition identity involving `B(tₙ)` and `B(tₙ₊₁)`.

The test carrier is still a finite increment history, not the full process-past sigma-algebra. No
conditional Markov theorem, Brownian process, or Yang--Mills measure is constructed.
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

omit [FiniteDimensional ℝ E] in
/-- Weak finite-increment-history identity for the actual current and future process values. The
ordered history product is replaced almost surely by `B(tₙ)`, and multiplying it by the final right
increment gives `B(tₙ₊₁)` in the fixed noncommutative orientation.

The history test still observes a finite increment vector. This theorem does not identify that
carrier with the full process-past sigma-algebra or state a conditional expectation. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.finiteIncrementHistory_process_weakMarkov_identity
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (times_zero : times 0 = 0) (t : NNReal) (ht : 0 < t)
    (final_time : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
    (Φ : C(Fin n → G, ℝ)) (f : C(G, ℝ)) :
    (∫ samplePoint,
      Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
        f (bridge.brownian.process (times (Fin.last (n + 1))) samplePoint)
      ∂bridge.brownian.probabilityMeasure) =
    ∫ samplePoint,
      Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (bridge.brownian.process (times (Fin.last n).castSucc) samplePoint)
      ∂bridge.brownian.probabilityMeasure := by
  have reconstructed :=
    bridge.brownian.pastRightIncrementProduct_ae_eq_currentState n times times_zero
  have transition :=
    bridge.finitePastIncrement_weakMarkov_identity n times times_monotone t ht final_time Φ
    (finiteRightIncrementHistoryProduct n) f
  calc
   _ = ∫ samplePoint, Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
      f (finiteRightIncrementHistoryProduct n
        (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
        twoDimensionalFinalRightIncrement bridge.brownian n times samplePoint)
      ∂bridge.brownian.probabilityMeasure := by
        apply integral_congr_ae
        filter_upwards [reconstructed] with samplePoint hrecon
        rw [show finiteRightIncrementHistoryProduct n
          (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) =
          twoDimensionalPastRightIncrementProduct bridge.brownian n times samplePoint by rfl]
        rw [hrecon]
        simp only [twoDimensionalFinalRightIncrement]
        group
   _ = _ := transition
   _ = _ := by
        apply integral_congr_ae
        filter_upwards [reconstructed] with samplePoint hrecon
        rw [show finiteRightIncrementHistoryProduct n
          (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) =
          twoDimensionalPastRightIncrementProduct bridge.brownian n times samplePoint by rfl]
        rw [hrecon]
end
end YangMills.Dimensions
