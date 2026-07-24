/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastIncrementIndependence
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridge

/-!
# Finite-past spectral transition identity

Finite mutual increment independence is connected here to the exact spectral heat operator. The
result permits an arbitrary continuous test of the complete first-`n` increment vector and an
arbitrary continuous current state extracted from that vector. Product-law transport and Fubini
then give the corresponding weak transition identity for the exact final increment.

This is a finite-history theorem, not conditioning on the full past sigma-algebra. It constructs no
Brownian process, heat kernel, Yang--Mills measure, or theory.
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
/-- Weak finite-history transition identity in increment coordinates. For every continuous real
history test `Φ`, every continuous state extracted from that history, and every continuous terminal
test `f`, integrating against the exact final increment agrees with applying the unchanged spectral
heat operator at that extracted state.

This quantifies over a finite increment-history vector only. It neither identifies that vector's
sigma-algebra with the full process past nor asserts a conditional-expectation theorem. -/
theorem TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData.finitePastIncrement_weakMarkov_identity
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
 (law := law) (inner := inner) (realLaplacian := realLaplacian)
 (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
 (n : ℕ) (times : Fin (n + 2) → NNReal) (hmono : Monotone times)
 (t : NNReal) (ht : 0 < t)
 (hfinal : times (Fin.last (n + 1)) = times (Fin.last n).castSucc + t)
 (Φ : C(Fin n → G, ℝ)) (state : C(Fin n → G, G)) (f : C(G, ℝ)) :
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
  let pairTest : C((Fin n → G) × G, ℝ) :=
    ⟨fun pair => Φ pair.1 * f (state pair.1 * pair.2),
      (Φ.continuous.comp continuous_fst).mul
        (f.continuous.comp ((state.continuous.comp continuous_fst).mul continuous_snd))⟩
  let stateTest : C(Fin n → G, ℝ) :=
    ⟨fun h => Φ h * bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f (state h),
      Φ.continuous.mul ((bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f).continuous.comp state.continuous)⟩
  have pairIntegrable : Integrable (fun pair : (Fin n → G) × G =>
      Φ pair.1 * f (state pair.1 * pair.2)) (μH.prod μt) := by
    have hc : Continuous (fun pair : (Fin n → G) × G =>
      Φ pair.1 * f (state pair.1 * pair.2)) := pairTest.continuous
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ := μH.prod μt) isCompact_univ
  have leftMap : (∫ pair, pairTest pair ∂Measure.map (fun samplePoint => (history samplePoint, final samplePoint))
      bridge.brownian.probabilityMeasure) =
      ∫ samplePoint, pairTest (history samplePoint, final samplePoint) ∂bridge.brownian.probabilityMeasure :=
    integral_map (history_meas.prodMk final_meas).aemeasurable pairTest.continuous.aestronglyMeasurable
  have rightMap : (∫ h, stateTest h ∂μH) =
      ∫ samplePoint, stateTest (history samplePoint) ∂bridge.brownian.probabilityMeasure :=
    integral_map history_meas.aemeasurable stateTest.continuous.aestronglyMeasurable
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
end
end YangMills.Dimensions
