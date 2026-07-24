/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSelectedLoopFinitePastIncrementIndependence
import YangMills.Mathematics.FiniteGroupIncrementTelescope

/-!
# Reconstructing the current process state from a finite increment history

The ordered product of a finite right-increment history is packaged as a continuous map. Exact
noncommutative telescoping identifies it with `B(t₀)⁻¹ B(tₙ)`. When the first evaluation time is zero,
the Brownian interface's almost-sure identity start therefore reconstructs the exact current process
state `B(tₙ)` from the history vector.

This is finite-dimensional process algebra. It does not identify a generated sigma-algebra with the
full past and does not assert a conditional Markov theorem.
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

/-- Continuous ordered product of an `n`-coordinate group-valued increment history. -/
def finiteRightIncrementHistoryProduct (n : ℕ) : C(Fin n → G, G) :=
  ⟨fun history => (List.ofFn history).prod, by
    simpa only [List.ofFn_eq_map] using
      continuous_list_prod (List.finRange n) (fun i _ => continuous_apply i)⟩

/-- Ordered product of the exact first `n` Brownian right increments. -/
def twoDimensionalPastRightIncrementProduct
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (samplePoint : Ω) : G :=
  finiteRightIncrementHistoryProduct n
    (twoDimensionalPastRightIncrements brownian n times samplePoint)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Exact endpoint formula before imposing the identity initial condition. -/
theorem TwoDimensionalSelectedLoopBrownianRealizationData.pastRightIncrementProduct_eq_endpoints
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (samplePoint : Ω) :
    twoDimensionalPastRightIncrementProduct brownian n times samplePoint =
      (brownian.process (times 0) samplePoint)⁻¹ *
        brownian.process (times (Fin.last n).castSucc) samplePoint := by
  unfold twoDimensionalPastRightIncrementProduct
  change (List.ofFn
    (twoDimensionalPastRightIncrements brownian n times samplePoint)).prod = _
  rw [show
    (List.ofFn (twoDimensionalPastRightIncrements brownian n times samplePoint)).prod =
      (List.ofFn (fun i : Fin n =>
        ((fun j : Fin (n + 1) => brownian.process (times j.castSucc) samplePoint)
          i.castSucc)⁻¹ *
        (fun j : Fin (n + 1) => brownian.process (times j.castSucc) samplePoint)
          i.succ)).prod by
      congr 2]
  simpa using finiteRightIncrementProduct_eq_endpoints n
    (fun j : Fin (n + 1) => brownian.process (times j.castSucc) samplePoint)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- If the finite time family starts at zero, the increment-history product reconstructs the exact
current process state almost surely under the unchanged Brownian probability law. -/
theorem TwoDimensionalSelectedLoopBrownianRealizationData.pastRightIncrementProduct_ae_eq_currentState
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin (n + 2) → NNReal) (times_zero : times 0 = 0) :
    ∀ᵐ samplePoint ∂brownian.probabilityMeasure,
      twoDimensionalPastRightIncrementProduct brownian n times samplePoint =
        brownian.process (times (Fin.last n).castSucc) samplePoint := by
  filter_upwards [brownian.process_zero] with samplePoint startsAtIdentity
  rw [brownian.pastRightIncrementProduct_eq_endpoints]
  rw [times_zero, startsAtIdentity]
  simp

end

end YangMills.Dimensions
