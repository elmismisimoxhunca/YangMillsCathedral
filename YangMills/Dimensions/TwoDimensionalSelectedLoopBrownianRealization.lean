/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatEquation
import Mathlib.Probability.Independence.Basic

/-!
# Brownian realization of the selected two-dimensional loop density

Driver constructs stochastic parallel transport from Lie-algebra white noise and identifies the
area-clocked group kernel. Sengupta defines `Q_t` as the density of standard Brownian motion governed
by the selected invariant metric. This module records a source-facing process realization of the
already connected density/semigroup/heat-equation chain.

The process starts at the identity almost surely, has almost-surely continuous paths, and has
stationary mutually independent right increments. The law of each positive increment is exactly the
unchanged normalized-Haar density measure. The one-time marginal is therefore derived, not stored as
a disconnected field; at the exact selected area it is proved equal to the sampled loop-holonomy
law.

This is uninhabited acceptance data. It constructs no probability space, stochastic process,
Brownian motion, Yang--Mills measure, or theory.
-/

namespace YangMills.Dimensions

open MeasureTheory ProbabilityTheory Filter
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection uΩ

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}

/-- Process realization of the exact same 2D selected-loop density chain, indexed by the general
compact Lie heat core rather than a compact-simple datum.

For monotone times `t₀ ≤ ... ≤ tₙ`, the increment indexed by `i` is
`B(tᵢ)⁻¹ B(tᵢ₊₁)`, matching the primitive convolution orientation already fixed by the project. -/
structure TwoDimensionalSelectedLoopBrownianRealizationData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (laplacian : RightInvariantPairingLaplacianData inner)
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (Ω : Type uΩ) [MeasurableSpace Ω] where
  /-- Probability law on the exact process sample carrier. -/
  probabilityMeasure : Measure Ω
  probability_normalized : probabilityMeasure Set.univ = 1
  /-- Group-valued process at nonnegative time. -/
  process : NNReal → Ω → G
  process_measurable : ∀ t, Measurable (process t)
  /-- Exact identity initial condition, almost surely under the same process law. -/
  process_zero : {samplePoint | process 0 samplePoint = 1} ∈ ae probabilityMeasure
  /-- Continuous paths under the same law. -/
  continuous_paths : {samplePoint | Continuous (fun t => process t samplePoint)} ∈
    ae probabilityMeasure
  /-- Every positive right increment has the unchanged density law at the elapsed time. -/
  stationary_increment_law : ∀ s t : NNReal, 0 < t →
    Measure.map (fun samplePoint =>
      (process s samplePoint)⁻¹ * process (s + t) samplePoint) probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ))
  /-- Mutual independence of every finite monotone family of consecutive right increments. -/
  independent_increments : ∀ n (t : Fin (n + 1) → NNReal), Monotone t →
    iIndepFun
      (fun (i : Fin n) samplePoint =>
        (process (t i.castSucc) samplePoint)⁻¹ * process (t i.succ) samplePoint)
      probabilityMeasure

namespace TwoDimensionalSelectedLoopBrownianRealizationData

variable
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    {heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian}

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The process probability measure cannot be zero. -/
theorem probabilityMeasure_ne_zero
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    brownian.probabilityMeasure ≠ 0 := by
  intro zero_measure
  have normalized := brownian.probability_normalized
  rw [zero_measure] at normalized
  simp at normalized

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The positive-time marginal is derived from the stationary increment at zero and the exact
almost-sure identity initial condition. -/
theorem marginal_law
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (t : NNReal) (ht : 0 < t) :
    Measure.map (brownian.process t) brownian.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ)) := by
  calc
    Measure.map (brownian.process t) brownian.probabilityMeasure =
        Measure.map
          (fun samplePoint =>
            (brownian.process 0 samplePoint)⁻¹ * brownian.process (0 + t) samplePoint)
          brownian.probabilityMeasure := by
      apply Measure.map_congr
      filter_upwards [brownian.process_zero] with samplePoint hzero
      simp [hzero]
    _ = (normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity (t : ℝ)) :=
      brownian.stationary_increment_law 0 t ht

/-- The selected strictly positive area as an exact nonnegative process time. -/
noncomputable def selectedAreaTime : NNReal :=
  ⟨law.enclosedArea, law.enclosedArea_pos.le⟩

omit [T2Space G] [SecondCountableTopology G] in
@[simp]
theorem selectedAreaTime_coe :
    ((selectedAreaTime (law := law) : NNReal) : ℝ) = law.enclosedArea :=
  rfl

omit [T2Space G] [SecondCountableTopology G] in
/-- The selected area time is strictly positive. -/
theorem selectedAreaTime_pos : 0 < selectedAreaTime (law := law) := by
  exact law.enclosedArea_pos

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- At the exact selected area, Brownian marginal and sampled loop holonomy have the same law. -/
theorem selectedArea_marginal_eq_sampledLoopLaw
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    Measure.map (brownian.process (selectedAreaTime (law := law)))
        brownian.probabilityMeasure =
      Measure.map
        (fun samplePoint =>
          base.holonomy law.selectedLoop (base.sampleConnection samplePoint))
        base.probabilityMeasure := by
  rw [brownian.marginal_law (selectedAreaTime (law := law)) selectedAreaTime_pos]
  rw [selectedAreaTime_coe]
  exact law.selectedLoop_law.symm

end TwoDimensionalSelectedLoopBrownianRealizationData

end

end YangMills.Dimensions
