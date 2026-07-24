/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopBrownianRealization

/-!
# Finite-past increment independence for the selected-loop Brownian interface

The Brownian acceptance surface already requires mutual independence of every finite monotone
family of consecutive right increments. This module packages the exact consequence needed for a
future finite-history Markov theorem: the vector of all first `n` increments is independent of the
last increment in an `(n+1)`-increment family.

This is stronger than pairwise current-state/increment independence, but it is still not
conditioning on the full past sigma-algebra and is not called a full Markov theorem. No process or
probability measure is constructed.
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

/-- Consecutive right increment with index `i` in a family of `n+1` increments determined by
`n+2` evaluation times. -/
def twoDimensionalConsecutiveRightIncrement
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (i : Fin (n + 1)) (samplePoint : Ω) : G :=
  (brownian.process (times i.castSucc) samplePoint)⁻¹ *
    brownian.process (times i.succ) samplePoint

/-- Vector of the first `n` consecutive right increments. -/
def twoDimensionalPastRightIncrements
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (samplePoint : Ω) (i : Fin n) : G :=
  (brownian.process (times i.castSucc.castSucc) samplePoint)⁻¹ *
    brownian.process (times i.castSucc.succ) samplePoint

/-- Last right increment, disjoint from the preceding `n`-increment history. -/
def twoDimensionalFinalRightIncrement
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (samplePoint : Ω) : G :=
  (brownian.process (times (Fin.last n).castSucc) samplePoint)⁻¹ *
    brownian.process (times (Fin.last (n + 1))) samplePoint

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The complete finite vector of past consecutive increments is independent of the final right
increment. The proof groups disjoint coordinates of the supplied mutually independent family; no
pairwise-independence shortcut is used. -/
theorem TwoDimensionalSelectedLoopBrownianRealizationData.pastRightIncrements_indep_final
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_monotone : Monotone times) :
    IndepFun (twoDimensionalPastRightIncrements brownian n times)
      (twoDimensionalFinalRightIncrement brownian n times)
      brownian.probabilityMeasure := by
  classical
  let increment : Fin (n + 1) → Ω → G := fun i =>
    twoDimensionalConsecutiveRightIncrement brownian n times i
  have increment_measurable : ∀ i, Measurable (increment i) := fun i =>
    (brownian.process_measurable (times i.castSucc)).inv.mul
      (brownian.process_measurable (times i.succ))
  have increments_independent : iIndepFun increment brownian.probabilityMeasure :=
    brownian.independent_increments (n + 1) times times_monotone
  let pastIndices : Finset (Fin (n + 1)) := Finset.univ.erase (Fin.last n)
  let finalIndex : Finset (Fin (n + 1)) := {Fin.last n}
  have indices_disjoint : Disjoint pastIndices finalIndex := by
    rw [Finset.disjoint_singleton_right]
    simp [pastIndices]
  have grouped := increments_independent.indepFun_finset
    pastIndices finalIndex indices_disjoint increment_measurable
  let pastProjection : (pastIndices → G) → (Fin n → G) := fun values i =>
    values ⟨i.castSucc, by simp [pastIndices]⟩
  let finalProjection : (finalIndex → G) → G := fun values =>
    values ⟨Fin.last n, Finset.mem_singleton_self _⟩
  have pastProjection_measurable : Measurable pastProjection := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply _
  have finalProjection_measurable : Measurable finalProjection := measurable_pi_apply _
  have result := grouped.comp pastProjection_measurable finalProjection_measurable
  change IndepFun
    (fun samplePoint (i : Fin n) =>
      (brownian.process (times i.castSucc.castSucc) samplePoint)⁻¹ *
        brownian.process (times i.castSucc.succ) samplePoint)
    (fun samplePoint =>
      (brownian.process (times (Fin.last n).castSucc) samplePoint)⁻¹ *
        brownian.process (times (Fin.last (n + 1))) samplePoint)
    brownian.probabilityMeasure
  simpa [increment, pastProjection, finalProjection,
    twoDimensionalConsecutiveRightIncrement, Function.comp_def] using result

end

end YangMills.Dimensions
