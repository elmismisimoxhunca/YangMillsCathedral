/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridge

/-!
# Hostile probes for spectral Brownian/generated-operator coherence
-/

namespace YangMills
namespace Dimensions
namespace TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridge
namespace Probes

open MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
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

/-- The stored Brownian process is indexed by the exact spectral heat core and semigroup. -/
noncomputable def exact_brownian_realization
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) :
    TwoDimensionalSelectedLoopBrownianRealizationData inner law
      bridge.spectralHeatKernel.convolutionSemigroup realLaplacian
      bridge.spectralHeatKernel.heatEquationCore Ω :=
  bridge.brownian

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Positive stationary increments have the exact spectral density. -/
theorem exact_stationary_increment_spectral_law
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (ht : 0 < t) :
    Measure.map (fun samplePoint =>
      (bridge.brownian.process s samplePoint)⁻¹ *
        bridge.brownian.process (s + t) samplePoint) bridge.brownian.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (t : ℝ)) :=
  bridge.stationary_increment_law_spectral s t ht

omit [FiniteDimensional ℝ E] in
/-- Successive positive process value/right-increment coordinates have the exact product of spectral
measures. -/
theorem exact_process_rightIncrement_joint_spectral_law
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (hs : 0 < s) (ht : 0 < t) :
    Measure.map (fun samplePoint =>
      (bridge.brownian.process s samplePoint,
        (bridge.brownian.process s samplePoint)⁻¹ *
          bridge.brownian.process (s + t) samplePoint)) bridge.brownian.probabilityMeasure =
      ((normalizedCompactHaarMeasure G).withDensity
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (s : ℝ))).prod
      ((normalizedCompactHaarMeasure G).withDensity
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (t : ℝ))) :=
  bridge.process_rightIncrement_joint_law_spectral s t hs ht

omit [FiniteDimensional ℝ E] in
/-- The exact two-time process law is the right-multiplication pushforward of the two spectral
factors. -/
theorem exact_process_twoTime_spectral_law
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (hs : 0 < s) (ht : 0 < t) :
    Measure.map (fun samplePoint =>
      (bridge.brownian.process s samplePoint,
        bridge.brownian.process (s + t) samplePoint)) bridge.brownian.probabilityMeasure =
      Measure.map (fun pair : G × G => (pair.1, pair.1 * pair.2))
        (((normalizedCompactHaarMeasure G).withDensity
          (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (s : ℝ))).prod
        ((normalizedCompactHaarMeasure G).withDensity
          (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (t : ℝ)))) :=
  bridge.process_twoTime_law_spectral s t hs ht

omit [FiniteDimensional ℝ E] in
/-- Hostile joint-law probe: an unrelated product measure cannot replace the exact two spectral
factors. -/
theorem changed_process_rightIncrement_joint_law_blocked
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (hs : 0 < s) (ht : 0 < t) (changed : Measure (G × G))
    (hchanged : changed ≠
      ((normalizedCompactHaarMeasure G).withDensity
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (s : ℝ))).prod
      ((normalizedCompactHaarMeasure G).withDensity
        (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (t : ℝ))))
    (changedLaw : Measure.map (fun samplePoint =>
      (bridge.brownian.process s samplePoint,
        (bridge.brownian.process s samplePoint)⁻¹ *
          bridge.brownian.process (s + t) samplePoint))
      bridge.brownian.probabilityMeasure = changed) : False := by
  apply hchanged
  rw [← changedLaw]
  exact bridge.process_rightIncrement_joint_law_spectral s t hs ht

omit [FiniteDimensional ℝ E] in
/-- At every deterministic base point, the generated operator is exactly the unconditional
expectation after right multiplication by a positive Brownian increment. -/
theorem exact_operator_right_increment_expectation
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (g : G) (s t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g =
      ∫ samplePoint, f (g * ((bridge.brownian.process s samplePoint)⁻¹ *
        bridge.brownian.process (s + t) samplePoint)) ∂bridge.brownian.probabilityMeasure :=
  bridge.generated_operator_eq_rightIncrementExpectation g s t ht f

omit [FiniteDimensional ℝ E] in
/-- Hostile base-point probe: changing the deterministic right-increment expectation is
contradictory. -/
theorem changed_operator_right_increment_expectation_blocked
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (g : G) (s t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (changed : ℝ)
    (hchanged : changed ≠
      ∫ samplePoint, f (g * ((bridge.brownian.process s samplePoint)⁻¹ *
        bridge.brownian.process (s + t) samplePoint)) ∂bridge.brownian.probabilityMeasure)
    (changedOperator :
      bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f g = changed) : False := by
  apply hchanged
  rw [← changedOperator]
  exact bridge.generated_operator_eq_rightIncrementExpectation g s t ht f

omit [FiniteDimensional ℝ E] in
/-- At the identity, the generated operator is exactly the unconditional expectation of every
continuous test of a positive Brownian right increment. -/
theorem exact_operator_increment_expectation
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) :
    bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f 1 =
      ∫ samplePoint, f ((bridge.brownian.process s samplePoint)⁻¹ *
        bridge.brownian.process (s + t) samplePoint) ∂bridge.brownian.probabilityMeasure :=
  bridge.generated_operator_one_eq_increment_expectation s t ht f

omit [FiniteDimensional ℝ E] in
/-- Hostile operator/process probe: changing the positive-increment expectation is contradictory. -/
theorem changed_operator_increment_expectation_blocked
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (ht : 0 < t) (f : C(G, ℝ)) (changed : ℝ)
    (hchanged : changed ≠
      ∫ samplePoint, f ((bridge.brownian.process s samplePoint)⁻¹ *
        bridge.brownian.process (s + t) samplePoint) ∂bridge.brownian.probabilityMeasure)
    (changedOperator :
      bridge.spectralHeatKernel.kernelOperator.heatOperator (t : ℝ) f 1 = changed) : False := by
  apply hchanged
  rw [← changedOperator]
  exact bridge.generated_operator_one_eq_increment_expectation s t ht f

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The same bridge exposes Driver's exact generated-operator derivative. -/
theorem exact_generated_operator
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    HasDerivAt (fun s => bridge.spectralHeatKernel.kernelOperator.heatOperator s f g)
      ((1 / 2 : ℝ) * realLaplacian.laplacian
        (bridge.spectralHeatKernel.kernelOperator.positiveTimeSmooth t ht f) g) t :=
  bridge.generated_operator_hasDerivAt t ht f g

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The Brownian selected-area marginal remains the unchanged sampled loop law. -/
theorem exact_selected_area_loop_law
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)) :
    Measure.map
        (bridge.brownian.process
          (TwoDimensionalSelectedLoopBrownianRealizationData.selectedAreaTime (law := law)))
        bridge.brownian.probabilityMeasure =
      Measure.map
        (fun samplePoint =>
          base.holonomy law.selectedLoop (base.sampleConnection samplePoint))
        base.probabilityMeasure :=
  bridge.brownian.selectedArea_marginal_eq_sampledLoopLaw

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Hostile stochastic-law probe: a changed positive increment measure is contradictory. -/
theorem changed_stationary_increment_law_blocked
    (bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω))
    (s t : NNReal) (ht : 0 < t) (changed : Measure G)
    (hchanged : changed ≠ (normalizedCompactHaarMeasure G).withDensity
      (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData (t : ℝ)))
    (changedLaw : Measure.map (fun samplePoint =>
      (bridge.brownian.process s samplePoint)⁻¹ *
        bridge.brownian.process (s + t) samplePoint)
      bridge.brownian.probabilityMeasure = changed) : False := by
  apply hchanged
  rw [← changedLaw]
  exact bridge.stationary_increment_law_spectral s t ht

end

end Probes
end TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridge
end Dimensions
end YangMills
