/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import YangMills.Foundation.Dimensions

/-!
# Gauge-fixed holonomy probability data in dimension two

This is the first source-specific continuum two-dimensional Yang--Mills acceptance surface. It
isolates the probability/holonomy nucleus of Driver's rigorous planar construction, with the
independent Gross--King--Sengupta, Sengupta, and Lévy constructions retained for later comparison.

The probability measure lives on an exact gauge-fixed sample carrier. Gauge transformations act on
a separate ambient connection carrier, not on the gauge-fixed slice: Driver explicitly warns that
fixing complete axial gauge loses manifest invariance. Random holonomy and physical observables are
obtained by restricting ambient functions along the exact sample-to-connection map. Only the
ambient physical observables are required to be gauge invariant.

No heat-kernel face law, subdivision/projective consistency, compact-surface gluing, or lattice
convergence is hidden here. Those require separate source-indexed interfaces. In particular this
record constructs neither a two-dimensional model nor any OS/Wightman or four-dimensional datum.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

/-- Source-facing nucleus of a gauge-fixed two-dimensional continuum holonomy law.

`concat γ δ` means first traverse `γ` and then `δ`. In Driver's parallel-transport convention this
gives `holonomy (concat γ δ) = holonomy δ * holonomy γ`. The gauge-fixed sample measure is not
required to be gauge invariant, and no gauge action on its slice carrier is assumed. -/
structure TwoDimensionalGaugeFixedHolonomyMeasureData
    (G Gauge Sample Connection : Type*) [Group G] [MeasurableSpace G]
    [Group Gauge] [MeasurableSpace Sample] where
  /-- Exact probability law on the gauge-fixed sample carrier. -/
  probabilityMeasure : Measure Sample
  /-- Probability normalization, retained on the exact gauge-fixed carrier. -/
  probability_normalized : probabilityMeasure Set.univ = 1
  /-- Exact inclusion/realization of a gauge-fixed sample as an ambient connection. -/
  sampleConnection : Sample → Connection
  /-- Source-specific admissible path carrier. -/
  Path : Type*
  /-- Source and target in literal two-dimensional Euclidean spacetime. -/
  pathSource : Path → EuclideanDimension.two.Spacetime
  pathTarget : Path → EuclideanDimension.two.Spacetime
  /-- Reversal and composable concatenation on the exact path class. -/
  reverse : Path → Path
  concat : Path → Path → Path
  composable : Path → Path → Prop
  composable_iff : ∀ γ δ, composable γ δ ↔ pathTarget γ = pathSource δ
  reverse_source : ∀ γ, pathSource (reverse γ) = pathTarget γ
  reverse_target : ∀ γ, pathTarget (reverse γ) = pathSource γ
  concat_source : ∀ γ δ, composable γ δ → pathSource (concat γ δ) = pathSource γ
  concat_target : ∀ γ δ, composable γ δ → pathTarget (concat γ δ) = pathTarget δ
  /-- A selected path prevents an empty path carrier from satisfying every path law vacuously. -/
  selectedPath : Path
  /-- Ambient parallel transport along every admissible path. -/
  holonomy : Path → Connection → G
  /-- Random holonomy is measurable only after restriction to the exact gauge-fixed law. -/
  sampledHolonomy_measurable : ∀ γ, Measurable (fun ω => holonomy γ (sampleConnection ω))
  holonomy_reverse : ∀ γ A, holonomy (reverse γ) A = (holonomy γ A)⁻¹
  holonomy_concat : ∀ γ δ A, composable γ δ →
    holonomy (concat γ δ) A = holonomy δ A * holonomy γ A
  /-- Gauge action on ambient connections; no action on the gauge-fixed sample carrier is required. -/
  gaugeAction : Gauge → Connection → Connection
  gaugeAction_one : ∀ A, gaugeAction 1 A = A
  gaugeAction_mul : ∀ g h A, gaugeAction (g * h) A = gaugeAction g (gaugeAction h A)
  /-- Endpoint value of a gauge transformation. -/
  gaugeValue : Gauge → EuclideanDimension.two.Spacetime → G
  gaugeValue_one : ∀ x, gaugeValue 1 x = 1
  gaugeValue_mul : ∀ g h x, gaugeValue (g * h) x = gaugeValue g x * gaugeValue h x
  /-- Driver-convention open-path covariance retains both endpoints and the exact ambient action. -/
  holonomy_gauge_covariant : ∀ g γ A,
    holonomy γ (gaugeAction g A) =
      gaugeValue g (pathTarget γ) * holonomy γ A *
        (gaugeValue g (pathSource γ))⁻¹
  /-- Exact designated physical-observable carrier. -/
  GaugeInvariantObservable : Type*
  /-- A selected observable prevents an empty physical-observable carrier. -/
  selectedObservable : GaugeInvariantObservable
  /-- Complex-valued physical observables on the ambient connection carrier. -/
  observable : GaugeInvariantObservable → Connection → ℂ
  /-- Measurability and integrability are asserted only after exact gauge-fixed restriction. -/
  sampledObservable_measurable : ∀ F,
    Measurable (fun ω => observable F (sampleConnection ω))
  sampledObservable_integrable : ∀ F,
    Integrable (fun ω => observable F (sampleConnection ω)) probabilityMeasure
  /-- Physical invariance concerns the ambient observable, not the gauge-fixed sample measure. -/
  observable_gauge_invariant : ∀ F g A,
    observable F (gaugeAction g A) = observable F A

namespace TwoDimensionalGaugeFixedHolonomyMeasureData

variable {G Gauge Sample Connection : Type*} [Group G] [MeasurableSpace G]
  [Group Gauge] [MeasurableSpace Sample]

/-- The normalized gauge-fixed probability measure cannot be the zero measure. -/
theorem probabilityMeasure_ne_zero
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection) :
    data.probabilityMeasure ≠ 0 := by
  intro zero_measure
  have normalized := data.probability_normalized
  rw [zero_measure] at normalized
  simp at normalized

/-- Expectation of a designated ambient physical observable under its exact gauge-fixed
restriction. -/
noncomputable def expectation
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (F : data.GaugeInvariantObservable) : ℂ :=
  ∫ ω, data.observable F (data.sampleConnection ω) ∂data.probabilityMeasure

/-- The same designated physical observable is unchanged by the exact ambient gauge action. -/
theorem observable_after_gauge
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (F : data.GaugeInvariantObservable) (g : Gauge) (A : Connection) :
    data.observable F (data.gaugeAction g A) = data.observable F A :=
  data.observable_gauge_invariant F g A

end TwoDimensionalGaugeFixedHolonomyMeasureData

end

end YangMills.Dimensions
