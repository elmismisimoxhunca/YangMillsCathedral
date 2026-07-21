/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGaugeFixedHolonomyMeasure
import YangMills.Mathematics.NormalizedCompactHaarMeasure

/-!
# Selected positive-area loop Haar-density law in dimension two

Driver's Theorem 6.4 expresses gauge-invariant planar expectations as finite Haar integrals with
one selected Haar density per bounded region. Sengupta's Theorem 4.8 and Proposition 4.9 state the
corresponding area-clocked lasso-holonomy density law directly.

This module records the smallest exact marginal: one closed path with strictly positive supplied
area, whose sampled holonomy pushforward is the selected Haar density against the canonical
probability-normalized compact Haar measure. One exact designated physical observable is tied to a
measurable conjugation-class function of that same holonomy, so its expectation formula is derived
rather than stored independently.

The path carrier still has no constructed planar embedding or simplicity predicate. More
importantly, the supplied density family is **not** called or characterized as a heat kernel here:
there is no invariant metric, Laplacian, Brownian law, heat equation, or convolution-semigroup
certificate. Those data are required by a later exact heat-kernel interface. Accordingly, this is
an uninhabited source-facing marginal shape, not a construction of the loop, its area, a density,
or a Yang--Mills measure. General face products, subdivision, gluing, and lattice convergence remain
separate obligations.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics

noncomputable section

/-- A selected closed-loop Haar-density marginal indexed by the exact gauge-fixed continuum nucleus.

The density is `ℝ≥0∞`-valued so that `Measure.withDensity` gives the exact measure-level statement
without a lossy conversion through real-valued representatives. -/
structure TwoDimensionalSelectedLoopHaarDensityLawData
    {G Gauge Sample Connection : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group Gauge] [MeasurableSpace Sample]
    (base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection) where
  /-- The exact selected loop in the source-specific admissible path carrier. -/
  selectedLoop : base.Path
  /-- The selected path is closed, so its ambient holonomy transforms by conjugation. -/
  selectedLoop_closed : base.pathSource selectedLoop = base.pathTarget selectedLoop
  /-- Supplied planar area enclosed by the selected loop. -/
  enclosedArea : ℝ
  /-- Zero-area and sign-reversed substitutes are excluded. -/
  enclosedArea_pos : 0 < enclosedArea
  /-- Supplied positive-area density family relative to normalized compact Haar. This field is not
  yet a heat-kernel characterization. -/
  selectedAreaDensity : ℝ → G → ENNReal
  selectedAreaDensity_measurable : ∀ t, 0 < t → Measurable (selectedAreaDensity t)
  /-- Required source symmetry of each positive-parameter density. -/
  selectedAreaDensity_central : ∀ t, 0 < t → ∀ h g,
    selectedAreaDensity t (h * g * h⁻¹) = selectedAreaDensity t g
  /-- The selected density relative to bi-invariant Haar measure is inversion symmetric. -/
  selectedAreaDensity_inv : ∀ t, 0 < t → ∀ g,
    selectedAreaDensity t g⁻¹ = selectedAreaDensity t g
  /-- Exact pushforward law of the same sampled holonomy under the same gauge-fixed probability. -/
  selectedLoop_law :
    Measure.map
        (fun ω => base.holonomy selectedLoop (base.sampleConnection ω))
        base.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity (selectedAreaDensity enclosedArea)
  /-- One exact existing physical observable represented by this same loop holonomy. -/
  physicalObservable : base.GaugeInvariantObservable
  /-- Measurable conjugation-class function used to interpret the selected physical observable. -/
  loopClassFunction : G → ℂ
  loopClassFunction_measurable : Measurable loopClassFunction
  loopClassFunction_central : ∀ h g,
    loopClassFunction (h * g * h⁻¹) = loopClassFunction g
  /-- Exact ambient interpretation bridge; no unrelated finite-dimensional observable is chosen. -/
  physicalObservable_eq_loopClassFunction : ∀ A,
    base.observable physicalObservable A = loopClassFunction (base.holonomy selectedLoop A)

namespace TwoDimensionalSelectedLoopHaarDensityLawData

variable {G Gauge Sample Connection : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [Group Gauge] [MeasurableSpace Sample]
  {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}

/-- Closedness specializes the exact open-path law to conjugation by the same endpoint value. -/
theorem selectedLoop_holonomy_gauge_conjugation
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (g : Gauge) (A : Connection) :
    base.holonomy law.selectedLoop (base.gaugeAction g A) =
      base.gaugeValue g (base.pathSource law.selectedLoop) *
        base.holonomy law.selectedLoop A *
          (base.gaugeValue g (base.pathSource law.selectedLoop))⁻¹ := by
  rw [base.holonomy_gauge_covariant]
  rw [← law.selectedLoop_closed]

/-- The selected Haar-density measure is normalized, derived from the exact pushforward of
the same gauge-fixed probability rather than accepted as a second probability field. -/
theorem densityMeasure_univ
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) :
    ((normalizedCompactHaarMeasure G).withDensity
      (law.selectedAreaDensity law.enclosedArea)) Set.univ = 1 := by
  rw [← law.selectedLoop_law]
  rw [Measure.map_apply
    (base.sampledHolonomy_measurable law.selectedLoop) MeasurableSet.univ]
  simpa using base.probability_normalized

/-- The selected Haar-density measure cannot be zero. -/
theorem densityMeasure_ne_zero
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) :
    (normalizedCompactHaarMeasure G).withDensity
      (law.selectedAreaDensity law.enclosedArea) ≠ 0 := by
  intro zero_measure
  have normalized := law.densityMeasure_univ
  rw [zero_measure] at normalized
  simp at normalized

/-- Driver/Sengupta selected-loop expectation formula, derived from the exact pushforward law and
the exact ambient observable interpretation bridge. -/
theorem physicalObservable_expectation_eq_selectedHaarDensityMeasure
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) :
    base.expectation law.physicalObservable =
      ∫ g, law.loopClassFunction g
        ∂((normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity law.enclosedArea)) := by
  rw [TwoDimensionalGaugeFixedHolonomyMeasureData.expectation]
  calc
    ∫ ω, base.observable law.physicalObservable (base.sampleConnection ω)
        ∂base.probabilityMeasure =
        ∫ ω, law.loopClassFunction
          (base.holonomy law.selectedLoop (base.sampleConnection ω))
          ∂base.probabilityMeasure := by
      apply integral_congr_ae
      filter_upwards with ω
      exact law.physicalObservable_eq_loopClassFunction (base.sampleConnection ω)
    _ = ∫ g, law.loopClassFunction g
          ∂(Measure.map
            (fun ω => base.holonomy law.selectedLoop (base.sampleConnection ω))
            base.probabilityMeasure) := by
      symm
      exact integral_map
        (base.sampledHolonomy_measurable law.selectedLoop).aemeasurable
        law.loopClassFunction_measurable.aestronglyMeasurable
    _ = ∫ g, law.loopClassFunction g
          ∂((normalizedCompactHaarMeasure G).withDensity
            (law.selectedAreaDensity law.enclosedArea)) := by
      rw [law.selectedLoop_law]

end TwoDimensionalSelectedLoopHaarDensityLawData

end

end YangMills.Dimensions
