/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastCylinderPiSystem

/-!
# Hostile probes for the concrete finite-past cylinder pi-system
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
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    {heat : TwoDimensionalSelectedLoopHeatEquationCoreData inner law semigroup laplacian}
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- A measurable event read at one concrete past time is a finite cylinder. -/
theorem singleton_evaluation_preimage_is_finiteCylinder
    (s : NNReal) (t : Set.Iic s) (event : Set G) (event_measurable : MeasurableSet event) :
    brownian.process t.1 ⁻¹' event ∈
      twoDimensionalSelectedLoopFinitePastCylinderSets brownian s := by
  refine ⟨{t}, ?_⟩
  have base_measurable :
      @MeasurableSet Ω
        (MeasurableSpace.comap (brownian.process t.1) inferInstance)
        (brownian.process t.1 ⁻¹' event) :=
    ⟨event, event_measurable, rfl⟩
  exact (le_iSup
    (fun u : ({t} : Finset (Set.Iic s)) =>
      MeasurableSpace.comap (brownian.process u.1.1) inferInstance)
    ⟨t, Finset.mem_singleton_self t⟩) _ base_measurable

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The finite supremum is exactly the pullback by its sorted coordinate vector. -/
theorem exact_orderedFiniteEvaluation_comap
    (s : NNReal) (times : Finset (Set.Iic s)) :
    twoDimensionalSelectedLoopFiniteEvaluationMeasurableSpace brownian s times =
      MeasurableSpace.comap
        (twoDimensionalSelectedLoopOrderedFiniteEvaluationMap brownian s times) inferInstance :=
  twoDimensionalSelectedLoopFiniteEvaluationMeasurableSpace_eq_comap brownian s times

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every cylinder has the exact measurable sorted-vector preimage representation. -/
theorem exact_finiteCylinder_coordinate_iff (s : NNReal) (set : Set Ω) :
    set ∈ twoDimensionalSelectedLoopFinitePastCylinderSets brownian s ↔
      ∃ (times : Finset (Set.Iic s)) (event : Set (Fin times.card → G)),
        MeasurableSet event ∧
          set = twoDimensionalSelectedLoopOrderedFiniteEvaluationMap brownian s times ⁻¹' event :=
  mem_twoDimensionalSelectedLoopFinitePastCylinderSets_iff brownian s set

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Empty finite histories retain exactly identity, current, and future times and remain monotone. -/
theorem empty_finiteCylinderTimeline_exact (s t : NNReal) :
    twoDimensionalSelectedLoopFiniteCylinderTimeline s t ∅ 0 = 0 ∧
    twoDimensionalSelectedLoopFiniteCylinderTimeline s t ∅ 1 = s ∧
    twoDimensionalSelectedLoopFiniteCylinderTimeline s t ∅ 2 = s + t ∧
    Monotone (twoDimensionalSelectedLoopFiniteCylinderTimeline s t ∅) := by
  refine ⟨rfl, ?_, ?_, twoDimensionalSelectedLoopFiniteCylinderTimeline_monotone s t ∅⟩
  · convert twoDimensionalSelectedLoopFiniteCylinderTimeline_current s t ∅ using 1
    congr 1
  · convert twoDimensionalSelectedLoopFiniteCylinderTimeline_future s t ∅ using 1
    congr 1

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Restricting the augmented history reads exactly the original sorted finite coordinates. -/
theorem exact_restrictedHistory_eq_orderedEvaluation
    (s t : NNReal) (times : Finset (Set.Iic s)) (samplePoint : Ω) :
    (fun i : Fin times.card =>
      twoDimensionalPastProcessValues brownian (times.card + 1)
        (twoDimensionalSelectedLoopFiniteCylinderTimeline s t times) samplePoint i.castSucc) =
      twoDimensionalSelectedLoopOrderedFiniteEvaluationMap brownian s times samplePoint :=
  twoDimensionalPastProcessValues_restrict_eq_orderedFiniteEvaluationMap
    brownian s t times samplePoint

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact generation probe: finite cylinders recover the full uncountable-time supremum. -/
theorem finiteCylinders_generate_exact_past (s : NNReal) :
    MeasurableSpace.generateFrom (twoDimensionalSelectedLoopFinitePastCylinderSets brownian s) =
      twoDimensionalSelectedLoopPastMeasurableSpace brownian s :=
  twoDimensionalSelectedLoopFinitePastCylinderSets_generateFrom_eq brownian s

variable
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : TwoDimensionalSelectedLoopSpectralBrownianGeneratorBridgeData
      (law := law) (inner := inner) (realLaplacian := realLaplacian)
      (complexLaplacian := complexLaplacian) (heatTraceData := heatTraceData) (Ω := Ω)}

omit [FiniteDimensional ℝ E] in
/-- The unchanged spectral Brownian bridge now constructs universal full-past semantics directly. -/
theorem exact_bridge_toFullPast :
    TwoDimensionalSelectedLoopFullPastMarkovData bridge :=
  bridge.toFinitePastCylinderMarkovData.toFullPastMarkovData

omit [FiniteDimensional ℝ E] in
/-- The same unchanged bridge constructs exact conditional-expectation Markov semantics. -/
theorem exact_bridge_fullPastConditional :
    bridge.HasFullPastConditionalMarkovProperty :=
  bridge.toFinitePastCylinderMarkovData.toPiSystemMarkovData.fullPastConditionalMarkov

omit [FiniteDimensional ℝ E] in
/-- The finite-cylinder set-integral record constructs universal full-past semantics. -/
theorem exact_finiteCylinder_toFullPast
    (data : TwoDimensionalSelectedLoopFinitePastCylinderMarkovData bridge) :
    TwoDimensionalSelectedLoopFullPastMarkovData bridge :=
  data.toFullPastMarkovData

omit [FiniteDimensional ℝ E] in
/-- Hostile finite-cylinder probe: an a.e.-different conditional version is rejected after closure. -/
theorem changed_finiteCylinder_conditional_blocked
    (data : TwoDimensionalSelectedLoopFinitePastCylinderMarkovData bridge)
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
  changed_ne_exact (claimed.symm.trans
    (data.toPiSystemMarkovData.fullPastConditionalMarkov s t ht f))

end

end YangMills.Dimensions
