/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFullPastMarkov

/-!
# Hostile probes for the exact full-past Markov surface
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

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every evaluation included in the past is measurable for that exact generated sigma-algebra. -/
theorem exact_process_measurable_past (s t : NNReal) (ht : t ≤ s) :
    @Measurable Ω G (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s) _
      (bridge.brownian.process t) :=
  bridge.brownian.process_measurable_past s t ht

omit [FiniteDimensional ℝ E] in
/-- Positive finite-cylinder probe, including exact past measurability and the transition identity. -/
theorem exact_finitePastCylinder_satisfies_fullPastTest
    (s t : NNReal) (ht : 0 < t)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times)
    (times_zero : times 0 = 0)
    (history_le : ∀ i : Fin n, times i.succ.castSucc ≤ s)
    (current_time : times (Fin.last n).castSucc = s)
    (future_time : times (Fin.last (n + 1)) = s + t)
    (test : (Fin n → G) → ℝ) (test_measurable : Measurable test)
    (bound : ℝ) (test_bound : ∀ history, ‖test history‖ ≤ bound)
    (f : C(G, ℝ)) :
    @Measurable Ω ℝ
        (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s) _
        (twoDimensionalFinitePastProcessTest bridge.brownian n times test) ∧
      (∫ samplePoint,
        twoDimensionalFinitePastProcessTest bridge.brownian n times test samplePoint *
          f (bridge.brownian.process (s + t) samplePoint)
        ∂bridge.brownian.probabilityMeasure) =
      ∫ samplePoint,
        twoDimensionalFinitePastProcessTest bridge.brownian n times test samplePoint *
          bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
            (bridge.brownian.process s samplePoint)
        ∂bridge.brownian.probabilityMeasure :=
  bridge.finitePastCylinder_satisfies_fullPastTest s t ht n times times_monotone times_zero
    history_le current_time future_time test test_measurable bound test_bound f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- A supplied full-past witness applies to every bounded past-measurable test, not merely finite
cylinders. -/
theorem exact_fullPast_arbitrary_test
    (data : TwoDimensionalSelectedLoopFullPastMarkovData bridge)
    (s t : NNReal) (ht : 0 < t) (pastTest : Ω → ℝ)
    (pastTest_measurable :
      @Measurable Ω ℝ
        (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s) _ pastTest)
    (pastTest_bounded : ∃ bound : ℝ, ∀ samplePoint, ‖pastTest samplePoint‖ ≤ bound)
    (f : C(G, ℝ)) :
    (∫ samplePoint, pastTest samplePoint * f (bridge.brownian.process (s + t) samplePoint)
      ∂bridge.brownian.probabilityMeasure) =
    ∫ samplePoint, pastTest samplePoint *
      bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
        (bridge.brownian.process s samplePoint)
      ∂bridge.brownian.probabilityMeasure :=
  data.fullPastWeakMarkov s t ht pastTest pastTest_measurable pastTest_bounded f

omit [FiniteDimensional ℝ E] in
/-- The two full-past formulations are exactly equivalent for the same process and spectral
operator; neither permits an unrelated conditioning sigma-algebra or transition family. -/
theorem exact_fullPast_semantics_equivalent :
    bridge.HasFullPastConditionalMarkovProperty ↔ bridge.HasFullPastWeakMarkovProperty :=
  bridge.fullPastConditionalMarkov_iff_weakMarkov

omit [FiniteDimensional ℝ E] in
/-- Hostile conditional-only probe: exact conditioning recovers the bounded weak test and rejects a
changed transition value without first assuming `TwoDimensionalSelectedLoopFullPastMarkovData`. -/
theorem conditional_fullPast_changed_weak_transition_blocked
    (conditional : bridge.HasFullPastConditionalMarkovProperty)
    (s t : NNReal) (ht : 0 < t) (pastTest : Ω → ℝ)
    (pastTest_measurable :
      @Measurable Ω ℝ
        (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s) _ pastTest)
    (pastTest_bounded : ∃ bound : ℝ, ∀ samplePoint, ‖pastTest samplePoint‖ ≤ bound)
    (f : C(G, ℝ)) (changed : ℝ)
    (changed_ne_exact : changed ≠
      ∫ samplePoint, pastTest samplePoint *
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (bridge.brownian.process s samplePoint)
        ∂bridge.brownian.probabilityMeasure)
    (claimed :
      (∫ samplePoint, pastTest samplePoint * f (bridge.brownian.process (s + t) samplePoint)
        ∂bridge.brownian.probabilityMeasure) = changed) : False := by
  have weak := bridge.fullPastConditionalMarkov_iff_weakMarkov.mp conditional
  rw [weak s t ht pastTest pastTest_measurable pastTest_bounded f] at claimed
  exact changed_ne_exact claimed.symm

omit [FiniteDimensional ℝ E] in
/-- A supplied universal weak full-past witness determines the exact conditional expectation. -/
theorem exact_fullPast_conditionalExpectation
    (data : TwoDimensionalSelectedLoopFullPastMarkovData bridge)
    (s t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) :
    MeasureTheory.condExp
        (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s)
        bridge.brownian.probabilityMeasure
        (fun samplePoint => f (bridge.brownian.process (s + t) samplePoint)) =ᵐ[
          bridge.brownian.probabilityMeasure]
      fun samplePoint =>
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (bridge.brownian.process s samplePoint) :=
  data.fullPastConditionalMarkov s t ht f

omit [FiniteDimensional ℝ E] in
/-- Hostile conditional probe: replacing the predicted version by an a.e.-different function is
incompatible with any supplied full-past witness. -/
theorem changed_fullPast_conditionalExpectation_blocked
    (data : TwoDimensionalSelectedLoopFullPastMarkovData bridge)
    (s t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (changed : Ω → ℝ)
    (changed_ne_exact : ¬ changed =ᵐ[bridge.brownian.probabilityMeasure]
      fun samplePoint =>
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (bridge.brownian.process s samplePoint))
    (claimed :
      MeasureTheory.condExp
          (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s)
          bridge.brownian.probabilityMeasure
          (fun samplePoint => f (bridge.brownian.process (s + t) samplePoint)) =ᵐ[
            bridge.brownian.probabilityMeasure] changed) : False :=
  changed_ne_exact (claimed.symm.trans (data.fullPastConditionalMarkov s t ht f))

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile full-past probe: a changed transition value contradicts any supplied full-past witness. -/
theorem changed_fullPast_transition_blocked
    (data : TwoDimensionalSelectedLoopFullPastMarkovData bridge)
    (s t : NNReal) (ht : 0 < t) (pastTest : Ω → ℝ)
    (pastTest_measurable :
      @Measurable Ω ℝ
        (twoDimensionalSelectedLoopPastMeasurableSpace bridge.brownian s) _ pastTest)
    (pastTest_bounded : ∃ bound : ℝ, ∀ samplePoint, ‖pastTest samplePoint‖ ≤ bound)
    (f : C(G, ℝ)) (changed : ℝ)
    (changed_ne_exact : changed ≠
      ∫ samplePoint, pastTest samplePoint *
        bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
          (bridge.brownian.process s samplePoint)
        ∂bridge.brownian.probabilityMeasure)
    (claimed :
      (∫ samplePoint, pastTest samplePoint * f (bridge.brownian.process (s + t) samplePoint)
        ∂bridge.brownian.probabilityMeasure) = changed) : False := by
  rw [data.fullPastWeakMarkov s t ht pastTest pastTest_measurable pastTest_bounded f] at claimed
  exact changed_ne_exact claimed.symm

end

end YangMills.Dimensions
