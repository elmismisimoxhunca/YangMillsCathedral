/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastIncrementIndependence

/-!
# Hostile probes for finite-past increment independence
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

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The theorem covers the whole finite history vector, not only one selected past increment. -/
theorem exact_finite_past_independence
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times) :
    IndepFun (twoDimensionalPastRightIncrements brownian n times)
      (twoDimensionalFinalRightIncrement brownian n times)
      brownian.probabilityMeasure :=
  brownian.pastRightIncrements_indep_final n times times_monotone

/-- Hostile overlap probe: every coordinate placed in the history is distinct from the final
increment coordinate. -/
theorem history_coordinate_ne_final (n : ℕ) (i : Fin n) :
    i.castSucc ≠ Fin.last n :=
  Fin.castSucc_ne_last i

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- At one history increment, the left side is literally the `0 → 1` right increment. -/
theorem one_step_history_exact (times : Fin 3 → NNReal) (samplePoint : Ω) :
    twoDimensionalPastRightIncrements brownian 1 times samplePoint 0 =
      (brownian.process (times 0) samplePoint)⁻¹ *
        brownian.process (times 1) samplePoint := by
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- At one history increment, the independent final coordinate is literally the `1 → 2` right
increment; replacing it by the overlapping first coordinate would change this expression. -/
theorem one_step_final_exact (times : Fin 3 → NNReal) (samplePoint : Ω) :
    twoDimensionalFinalRightIncrement brownian 1 times samplePoint =
      (brownian.process (times 1) samplePoint)⁻¹ *
        brownian.process (times 2) samplePoint := by
  rfl

end

end YangMills.Dimensions
