/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFiniteHistoryProcessTransition

/-!
# Bounded-measurable finite-history spectral transition

The finite-history transition law is extended from continuous history tests to arbitrary bounded
measurable real tests. Integrability is derived from the explicit history bound, compactness of the
continuous terminal factor, and finiteness of the exact history and spectral measures.

The resulting process-history theorem still ranges over fixed finite evaluation vectors. It is a
key monotone-class precursor, not conditioning on the full past sigma-algebra.
-/

namespace YangMills.Dimensions
open MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff
noncomputable section
universe uE uG uGauge uSample uConnection uΩ
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [SecondCountableTopology G]
 [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G]
 [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
 {Gauge : Type uGauge} [Group Gauge] {Sample : Type uSample} [MeasurableSpace Sample]
 {Connection : Type uConnection} {Ω : Type uΩ} [MeasurableSpace Ω]
 {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
 {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
 {inner : Geometry.InvariantInnerProductData (I := modelWithCornersSelf ℝ E) (G := G)}
 {realLaplacian : RightInvariantPairingLaplacianData inner}
 {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
 {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

omit [FiniteDimensional ℝ E] in
/-- Weak transition identity for a bounded measurable finite increment-history test. The state
extracted from the history and the terminal test remain continuous, matching the existing spectral
operator interface. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.finitePastIncrement_boundedMeasurable_weakMarkov_identity
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
 (law := law) (inner := inner) (realLaplacian := realLaplacian)
 (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
 (n : ℕ) (times : Fin (n + 2) → NNReal) (hmono : Monotone times)
 (t : NNReal) (ht : 0 < t)
 (hfinal : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
 (Φ : (Fin n → G) → ℝ) (Φ_meas : Measurable Φ) (C : ℝ) (Φ_bound : ∀ h, ‖Φ h‖ ≤ C)
 (state : C(Fin n → G, G)) (f : C(G, ℝ)) :
 (∫ samplePoint, Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
   f (state (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
     twoDimensionalFinalRightIncrement bridge.brownian n times samplePoint)
   ∂bridge.brownian.probabilityMeasure) =
 (∫ samplePoint, Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
   bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f
     (state (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint))
   ∂bridge.brownian.probabilityMeasure) := by
  let history : Ω → (Fin n → G) := twoDimensionalPastRightIncrements bridge.brownian n times
  let final : Ω → G := twoDimensionalFinalRightIncrement bridge.brownian n times
  have history_meas : Measurable history := by
    apply measurable_pi_iff.mpr
    intro i
    exact (bridge.brownian.process_measurable (times i.castSucc.castSucc)).inv.mul
      (bridge.brownian.process_measurable (times i.castSucc.succ))
  have final_meas : Measurable final :=
    (bridge.brownian.process_measurable (times (Fin.last n).castSucc)).inv.mul
      (bridge.brownian.process_measurable (times (Fin.last (n + 1))))
  let μH : Measure (Fin n → G) := Measure.map history bridge.brownian.probabilityMeasure
  let μt : Measure G := unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData (t : ℝ)
  letI : IsFiniteMeasure bridge.brownian.probabilityMeasure :=
    ⟨by rw [bridge.brownian.probability_normalized]; exact ENNReal.one_lt_top⟩
  letI : IsFiniteMeasure μH := by infer_instance
  letI : IsFiniteMeasure μt :=
    ⟨by rw [unitaryMatrixDualCasimirHeatProbabilityMeasure_univ
      bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.casimirBridge
      bridge.spectralHeatKernel.heatEquationBridge.spectralDensityBridge.positivity
      (by exact_mod_cast ht)]; exact ENNReal.one_lt_top⟩
  have final_map : Measure.map final bridge.brownian.probabilityMeasure = μt := by
    rw [show final = fun samplePoint =>
      (bridge.brownian.process (times (Fin.last n).castSucc) samplePoint)⁻¹ *
      bridge.brownian.process (times (Fin.last n).castSucc + t) samplePoint by
        funext samplePoint
        simp only [final, twoDimensionalFinalRightIncrement]
        rw [hfinal]]
    exact bridge.stationary_increment_law_spectral (times (Fin.last n).castSucc) t ht
  have joint := (bridge.brownian.pastRightIncrements_indep_final n times hmono)
    |>.map_prod_eq_prod_map_map history_meas.aemeasurable final_meas.aemeasurable
  rw [final_map] at joint
  let pairTest : ((Fin n → G) × G) → ℝ := fun pair => Φ pair.1 * f (state pair.1 * pair.2)
  let stateTest : (Fin n → G) → ℝ := fun h =>
    Φ h * bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f (state h)
  have pairTest_meas : Measurable pairTest :=
    (Φ_meas.comp measurable_fst).mul
      (f.continuous.measurable.comp ((state.continuous.measurable.comp measurable_fst).mul measurable_snd))
  have stateTest_meas : Measurable stateTest :=
    Φ_meas.mul ((bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f).continuous.measurable.comp
      state.continuous.measurable)
  have coreIntegrable : Integrable (fun pair : (Fin n → G) × G => f (state pair.1 * pair.2))
      (μH.prod μt) := by
    have hc : Continuous (fun pair : (Fin n → G) × G => f (state pair.1 * pair.2)) :=
      f.continuous.comp ((state.continuous.comp continuous_fst).mul continuous_snd)
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ := μH.prod μt) isCompact_univ
  have pairIntegrable : Integrable pairTest (μH.prod μt) := by
    apply coreIntegrable.bdd_mul (Φ_meas.comp measurable_fst).aestronglyMeasurable
    filter_upwards [] with pair
    exact Φ_bound pair.1
  have leftMap : (∫ pair, pairTest pair ∂Measure.map (fun samplePoint => (history samplePoint, final samplePoint))
      bridge.brownian.probabilityMeasure) =
      ∫ samplePoint, pairTest (history samplePoint, final samplePoint) ∂bridge.brownian.probabilityMeasure :=
    integral_map (history_meas.prodMk final_meas).aemeasurable pairTest_meas.aestronglyMeasurable
  have rightMap : (∫ h, stateTest h ∂μH) =
      ∫ samplePoint, stateTest (history samplePoint) ∂bridge.brownian.probabilityMeasure :=
    integral_map history_meas.aemeasurable stateTest_meas.aestronglyMeasurable
  change (∫ samplePoint, pairTest (history samplePoint, final samplePoint) ∂bridge.brownian.probabilityMeasure) =
    ∫ samplePoint, stateTest (history samplePoint) ∂bridge.brownian.probabilityMeasure
  calc
    _ = ∫ pair, pairTest pair ∂Measure.map (fun samplePoint => (history samplePoint, final samplePoint))
        bridge.brownian.probabilityMeasure := leftMap.symm
    _ = ∫ pair, pairTest pair ∂μH.prod μt := by rw [joint]
    _ = ∫ h, ∫ y, Φ h * f (state h * y) ∂μt ∂μH := integral_prod _ pairIntegrable
    _ = ∫ h, stateTest h ∂μH := by
      apply integral_congr_ae
      filter_upwards [] with h
      change (∫ y, Φ h * f (state h * y) ∂μt) =
        Φ h * bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f (state h)
      rw [bridge.generated_operator_eq_spectralMeasureIntegral (t : ℝ) (by exact_mod_cast ht) f (state h)]
      rw [integral_const_mul]
    _ = _ := rightMap

omit [FiniteDimensional ℝ E] in
/-- Weak Markov identity for arbitrary bounded measurable tests of the actual finite process-
evaluation history `(B(t₁),…,B(tₙ))`. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.finiteProcessHistory_boundedMeasurable_weakMarkov_identity
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
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
      ∂bridge.brownian.probabilityMeasure := by
  let Φ : (Fin n → G) → ℝ := fun history =>
    Ψ (finiteRightIncrementPrefixProductsContinuousMap n history)
  have Φ_measurable : Measurable Φ :=
    Ψ_measurable.comp (finiteRightIncrementPrefixProductsContinuousMap n).continuous.measurable
  have Φ_bound : ∀ history, ‖Φ history‖ ≤ bound := fun history => Ψ_bound _
  have processHistory_reconstructed :=
    bridge.brownian.pastRightIncrementPrefixProducts_ae_eq_processValues n times times_zero
  have currentState_reconstructed :=
    bridge.brownian.pastRightIncrementProduct_ae_eq_currentState n times times_zero
  have transition := bridge.finitePastIncrement_boundedMeasurable_weakMarkov_identity
    n times times_monotone t ht final_time Φ Φ_measurable bound Φ_bound
      (finiteRightIncrementHistoryProduct n) f
  calc
    _ = ∫ samplePoint,
        Φ (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
          f (finiteRightIncrementHistoryProduct n
              (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) *
            twoDimensionalFinalRightIncrement bridge.brownian n times samplePoint)
        ∂bridge.brownian.probabilityMeasure := by
      apply integral_congr_ae
      filter_upwards [processHistory_reconstructed, currentState_reconstructed]
        with samplePoint hhistory hcurrent
      simp only [Φ]
      rw [hhistory]
      rw [show finiteRightIncrementHistoryProduct n
        (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) =
          twoDimensionalPastRightIncrementProduct bridge.brownian n times samplePoint by rfl]
      rw [hcurrent]
      simp only [twoDimensionalFinalRightIncrement]
      group
    _ = _ := transition
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [processHistory_reconstructed, currentState_reconstructed]
        with samplePoint hhistory hcurrent
      simp only [Φ]
      rw [hhistory]
      rw [show finiteRightIncrementHistoryProduct n
        (twoDimensionalPastRightIncrements bridge.brownian n times samplePoint) =
          twoDimensionalPastRightIncrementProduct bridge.brownian n times samplePoint by rfl]
      rw [hcurrent]

end

end YangMills.Dimensions
