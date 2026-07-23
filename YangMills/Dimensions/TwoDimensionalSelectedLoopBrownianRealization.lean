/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatEquation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Brownian realization of the selected two-dimensional loop density

Driver constructs stochastic parallel transport from Lie-algebra white noise and identifies the
area-clocked group kernel. Sengupta defines `Q_t` as the density of standard Brownian motion governed
by the selected invariant metric. This module records a source-facing process realization of the
already connected density/semigroup/heat-equation chain.

The process starts at the identity almost surely, has almost-surely continuous paths, and has
stationary mutually independent right increments. A measurable null hull of the discontinuous-path
set yields an everywhere-continuous jointly `NNReal × Ω` measurable modification, simultaneously
almost surely equal at every time and preserving all fixed-time and stationary-increment laws. The law of each positive increment is exactly the
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
    [MeasurableMul₂ G] [MeasurableInv G]
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

/-- Set of sample points where the supplied process path is not continuous. -/
def pathDiscontinuitySet
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) : Set Ω :=
  {samplePoint | Continuous (fun t => brownian.process t samplePoint)}ᶜ

/-- A measurable null hull of all path-discontinuity points. -/
def pathDiscontinuityHull
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) : Set Ω :=
  toMeasurable brownian.probabilityMeasure brownian.pathDiscontinuitySet

/-- Modify the process to the identity on the measurable null discontinuity hull. This preserves the
original process almost surely and gives continuous paths at every sample point. -/
noncomputable def jointlyMeasurableProcess
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) : NNReal → Ω → G := by
  classical
  exact fun t samplePoint =>
    if samplePoint ∈ brownian.pathDiscontinuityHull then 1 else brownian.process t samplePoint

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The measurable path-discontinuity hull is null. -/
theorem pathDiscontinuityHull_null
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    brownian.probabilityMeasure brownian.pathDiscontinuityHull = 0 := by
  rw [pathDiscontinuityHull, measure_toMeasurable]
  have continuousAlmostEverywhere :=
    (mem_ae_iff.mp brownian.continuous_paths)
  simpa [pathDiscontinuitySet] using continuousAlmostEverywhere

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The modified process agrees with the original process for every time simultaneously, almost
surely under the unchanged process law. -/
theorem jointlyMeasurableProcess_ae_eq
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    ∀ᵐ samplePoint ∂brownian.probabilityMeasure,
      ∀ t, brownian.jointlyMeasurableProcess t samplePoint = brownian.process t samplePoint := by
  have outsideHull : brownian.pathDiscontinuityHullᶜ ∈ ae brownian.probabilityMeasure := by
    rw [mem_ae_iff]
    simpa using brownian.pathDiscontinuityHull_null
  filter_upwards [outsideHull] with samplePoint outside
  intro t
  have notInHull : samplePoint ∉ brownian.pathDiscontinuityHull := outside
  simp [jointlyMeasurableProcess, notInHull]

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every path of the null-hull modification is continuous, including points outside the original
almost-sure continuous-path event. -/
theorem jointlyMeasurableProcess_continuous
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (samplePoint : Ω) :
    Continuous (fun t => brownian.jointlyMeasurableProcess t samplePoint) := by
  classical
  by_cases inHull : samplePoint ∈ brownian.pathDiscontinuityHull
  · simp only [jointlyMeasurableProcess, if_pos inHull]
    exact continuous_const
  · simp only [jointlyMeasurableProcess, if_neg inHull]
    have outsideBad : samplePoint ∉ brownian.pathDiscontinuitySet := by
      intro badMembership
      exact inHull (subset_toMeasurable brownian.probabilityMeasure
        brownian.pathDiscontinuitySet badMembership)
    simpa [pathDiscontinuitySet] using outsideBad

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every fixed-time slice of the null-hull modification is measurable. -/
theorem jointlyMeasurableProcess_fixedTime_measurable
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (t : NNReal) : Measurable (brownian.jointlyMeasurableProcess t) := by
  classical
  exact Measurable.ite (measurableSet_toMeasurable _ _)
    measurable_const (brownian.process_measurable t)

omit [FiniteDimensional ℝ E]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The modified process is jointly measurable on `NNReal × Ω`, derived from everywhere-continuous
paths and measurable fixed-time slices. -/
theorem jointlyMeasurableProcess_measurable
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    Measurable (Function.uncurry brownian.jointlyMeasurableProcess) := by
  letI : MetricSpace G := TopologicalSpace.metrizableSpaceMetric G
  exact measurable_uncurry_of_continuous_of_measurable
    brownian.jointlyMeasurableProcess_continuous
    brownian.jointlyMeasurableProcess_fixedTime_measurable

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The jointly measurable modification still starts at the exact identity almost surely. -/
theorem jointlyMeasurableProcess_zero
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    {samplePoint | brownian.jointlyMeasurableProcess 0 samplePoint = 1} ∈
      ae brownian.probabilityMeasure := by
  filter_upwards [brownian.jointlyMeasurableProcess_ae_eq, brownian.process_zero]
    with samplePoint equality startsAtOne
  rw [equality 0]
  exact startsAtOne

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every finite monotone family of consecutive modified right increments retains mutual
independence. -/
theorem jointlyMeasurableProcess_independent_increments
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (t : Fin (n + 1) → NNReal) (ht : Monotone t) :
    iIndepFun
      (fun (i : Fin n) samplePoint =>
        (brownian.jointlyMeasurableProcess (t i.castSucc) samplePoint)⁻¹ *
          brownian.jointlyMeasurableProcess (t i.succ) samplePoint)
      brownian.probabilityMeasure := by
  apply (brownian.independent_increments n t ht).congr
  intro i
  filter_upwards [brownian.jointlyMeasurableProcess_ae_eq] with samplePoint equality
  rw [equality (t i.castSucc), equality (t i.succ)]

/-- Repackage the null-hull modification as a Brownian-realization datum on the exact same sample
carrier and probability measure. All required laws are derived rather than resupplied. -/
noncomputable def jointlyMeasurableVersion
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω where
  probabilityMeasure := brownian.probabilityMeasure
  process := brownian.jointlyMeasurableProcess
  process_measurable := brownian.jointlyMeasurableProcess_fixedTime_measurable
  process_zero := brownian.jointlyMeasurableProcess_zero
  continuous_paths := Filter.Eventually.of_forall
    brownian.jointlyMeasurableProcess_continuous
  stationary_increment_law := by
    intro s t ht
    calc
      Measure.map (fun samplePoint =>
          (brownian.jointlyMeasurableProcess s samplePoint)⁻¹ *
            brownian.jointlyMeasurableProcess (s + t) samplePoint)
          brownian.probabilityMeasure =
        Measure.map (fun samplePoint =>
          (brownian.process s samplePoint)⁻¹ * brownian.process (s + t) samplePoint)
          brownian.probabilityMeasure := by
        apply Measure.map_congr
        filter_upwards [brownian.jointlyMeasurableProcess_ae_eq] with samplePoint equality
        rw [equality s, equality (s + t)]
      _ = (normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity (t : ℝ)) := brownian.stationary_increment_law s t ht
  independent_increments := brownian.jointlyMeasurableProcess_independent_increments

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem jointlyMeasurableVersion_probabilityMeasure
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    brownian.jointlyMeasurableVersion.probabilityMeasure = brownian.probabilityMeasure :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem jointlyMeasurableVersion_process
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    brownian.jointlyMeasurableVersion.process = brownian.jointlyMeasurableProcess :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The repackaged version exposes the jointly measurable process without changing its carrier or
probability law. -/
theorem jointlyMeasurableVersion_process_measurable
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    Measurable (Function.uncurry brownian.jointlyMeasurableVersion.process) := by
  rw [jointlyMeasurableVersion_process]
  exact brownian.jointlyMeasurableProcess_measurable

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every fixed-time law of the jointly measurable modification equals the original fixed-time law. -/
theorem jointlyMeasurableProcess_map_eq
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) (t : NNReal) :
    Measure.map (brownian.jointlyMeasurableProcess t) brownian.probabilityMeasure =
      Measure.map (brownian.process t) brownian.probabilityMeasure := by
  apply Measure.map_congr
  filter_upwards [brownian.jointlyMeasurableProcess_ae_eq] with samplePoint equality
  exact equality t

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every finite vector of modified time evaluations is measurable. -/
theorem jointlyMeasurableProcess_finiteTime_measurable
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin n → NNReal) :
    Measurable (fun samplePoint i =>
      brownian.jointlyMeasurableProcess (times i) samplePoint) := by
  apply measurable_pi_iff.mpr
  intro i
  exact brownian.jointlyMeasurableProcess_fixedTime_measurable (times i)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The modification preserves every finite-dimensional process distribution, not only individual
fixed-time marginals. -/
theorem jointlyMeasurableProcess_finiteDimensionalDistribution_eq
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (times : Fin n → NNReal) :
    Measure.map (fun samplePoint i =>
        brownian.jointlyMeasurableProcess (times i) samplePoint)
        brownian.probabilityMeasure =
      Measure.map (fun samplePoint i => brownian.process (times i) samplePoint)
        brownian.probabilityMeasure := by
  apply Measure.map_congr
  filter_upwards [brownian.jointlyMeasurableProcess_ae_eq] with samplePoint equality
  funext i
  exact equality (times i)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every positive stationary right-increment law is unchanged by the jointly measurable
modification. -/
theorem jointlyMeasurableProcess_stationary_increment_law
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (s t : NNReal) (ht : 0 < t) :
    Measure.map (fun samplePoint =>
      (brownian.jointlyMeasurableProcess s samplePoint)⁻¹ *
        brownian.jointlyMeasurableProcess (s + t) samplePoint) brownian.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ)) := by
  calc
    Measure.map (fun samplePoint =>
        (brownian.jointlyMeasurableProcess s samplePoint)⁻¹ *
          brownian.jointlyMeasurableProcess (s + t) samplePoint) brownian.probabilityMeasure =
      Measure.map (fun samplePoint =>
        (brownian.process s samplePoint)⁻¹ * brownian.process (s + t) samplePoint)
        brownian.probabilityMeasure := by
      apply Measure.map_congr
      filter_upwards [brownian.jointlyMeasurableProcess_ae_eq] with samplePoint equality
      rw [equality s, equality (s + t)]
    _ = (normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity (t : ℝ)) := brownian.stationary_increment_law s t ht

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- At every nonnegative time, the process value is independent of its following right increment.
This is derived from mutual independence of the two consecutive increments at times `0,s,s+t` and
the almost-sure identity start; it is not an additional Markov assumption. -/
theorem process_indep_rightIncrement
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (s t : NNReal) :
    brownian.process s ⟂ᵢ[brownian.probabilityMeasure]
      (fun samplePoint =>
        (brownian.process s samplePoint)⁻¹ * brownian.process (s + t) samplePoint) := by
  let times : Fin 3 → NNReal := ![0, s, s + t]
  have times_monotone : Monotone times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times]
  have increments_independent :=
    (brownian.independent_increments 2 times times_monotone).indepFun
      (show (0 : Fin 2) ≠ 1 by decide)
  apply increments_independent.congr
  · filter_upwards [brownian.process_zero] with samplePoint startsAtOne
    simp [times, startsAtOne]
  · exact Filter.EventuallyEq.rfl

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The stationary increment law at one positive time derives normalization of the process carrier;
it is not an independent acceptance field. -/
theorem probability_normalized
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    brownian.probabilityMeasure Set.univ = 1 := by
  let increment : Ω → G := fun samplePoint =>
    (brownian.process 0 samplePoint)⁻¹ * brownian.process (0 + 1) samplePoint
  have increment_measurable : Measurable increment :=
    (brownian.process_measurable 0).inv.mul (brownian.process_measurable (0 + 1))
  calc
    brownian.probabilityMeasure Set.univ =
        Measure.map increment brownian.probabilityMeasure Set.univ := by
      rw [Measure.map_apply increment_measurable MeasurableSet.univ, Set.preimage_univ]
    _ = ((normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity (1 : ℝ))) Set.univ := by
      simpa [increment] using congrArg (fun measure : Measure G => measure Set.univ)
        (brownian.stationary_increment_law 0 1 zero_lt_one)
    _ = 1 := semigroup.densityMeasure_univ_of_pos 1 zero_lt_one

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

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
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

omit [T2Space G] [SecondCountableTopology G] [MeasurableMul₂ G] [MeasurableInv G] in
@[simp]
theorem selectedAreaTime_coe :
    ((selectedAreaTime (law := law) : NNReal) : ℝ) = law.enclosedArea :=
  rfl

omit [T2Space G] [SecondCountableTopology G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The selected area time is strictly positive. -/
theorem selectedAreaTime_pos : 0 < selectedAreaTime (law := law) := by
  exact law.enclosedArea_pos

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
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

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The jointly measurable version retains the exact selected-area equality with the sampled loop
holonomy law. -/
theorem jointlyMeasurableProcess_selectedArea_marginal_eq_sampledLoopLaw
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    Measure.map
        (brownian.jointlyMeasurableProcess (selectedAreaTime (law := law)))
        brownian.probabilityMeasure =
      Measure.map
        (fun samplePoint =>
          base.holonomy law.selectedLoop (base.sampleConnection samplePoint))
        base.probabilityMeasure := by
  rw [brownian.jointlyMeasurableProcess_map_eq]
  exact brownian.selectedArea_marginal_eq_sampledLoopLaw

end TwoDimensionalSelectedLoopBrownianRealizationData

end

end YangMills.Dimensions
