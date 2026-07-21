/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalGaugeFixedHolonomyMeasure

/-!
# Hostile probes for the two-dimensional gauge-fixed holonomy law

These probes expose probability normalization, exact restriction to the gauge-fixed slice,
nonempty designated path/observable carriers, endpoint-aware ambient covariance, reversal,
concatenation, and the literal dimension-two index. They do not add heat-kernel, gluing,
lattice-convergence, OS, or Wightman claims.
-/

namespace YangMills.Dimensions.TwoDimensionalGaugeFixedHolonomyMeasure.Probes

open MeasureTheory

noncomputable section

variable {G Gauge Sample Connection : Type*} [Group G] [MeasurableSpace G]
  [Group Gauge] [MeasurableSpace Sample]

/-- Probability normalization blocks the disconnected zero measure. -/
theorem zero_probability_measure_blocked
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (claimed : data.probabilityMeasure = 0) : False :=
  data.probabilityMeasure_ne_zero claimed

/-- The exact path carrier has a designated element and therefore cannot be empty. -/
theorem path_carrier_nonempty
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection) :
    Nonempty data.Path :=
  ⟨data.selectedPath⟩

/-- The exact physical-observable carrier has a designated element. -/
theorem observable_carrier_nonempty
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection) :
    Nonempty data.GaugeInvariantObservable :=
  ⟨data.selectedObservable⟩

/-- Open-path covariance exposes both endpoints and the same designated ambient action. -/
theorem exact_open_path_endpoint_covariance
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (g : Gauge) (γ : data.Path) (A : Connection) :
    data.holonomy γ (data.gaugeAction g A) =
      data.gaugeValue g (data.pathTarget γ) * data.holonomy γ A *
        (data.gaugeValue g (data.pathSource γ))⁻¹ :=
  data.holonomy_gauge_covariant g γ A

/-- A wrong reversal value is incompatible with the exact ambient holonomy chain. -/
theorem wrong_reverse_holonomy_blocked
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (γ : data.Path) (A : Connection) (wrong : G)
    (different : wrong ≠ (data.holonomy γ A)⁻¹)
    (claimed : data.holonomy (data.reverse γ) A = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.holonomy_reverse γ A

/-- A wrong Driver-convention composable concatenation value is rejected. -/
theorem wrong_concat_holonomy_blocked
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (γ δ : data.Path) (A : Connection) (hcomp : data.composable γ δ) (wrong : G)
    (different : wrong ≠ data.holonomy δ A * data.holonomy γ A)
    (claimed : data.holonomy (data.concat γ δ) A = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.holonomy_concat γ δ A hcomp

/-- Random holonomy is tied to the exact sample-to-ambient restriction map. -/
theorem exact_sampled_holonomy_measurable
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (γ : data.Path) :
    Measurable (fun ω => data.holonomy γ (data.sampleConnection ω)) :=
  data.sampledHolonomy_measurable γ

/-- The designated physical observable is invariant under the exact ambient action, rather than
under a convenient action chosen inside the statement. -/
theorem exact_designated_observable_invariance
    (data : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection)
    (F : data.GaugeInvariantObservable) (g : Gauge) (A : Connection) :
    data.observable F (data.gaugeAction g A) = data.observable F A :=
  data.observable_after_gauge F g A

/-- This source-specific lower-dimensional law cannot change the Clay endpoint index. -/
theorem two_dimensional_law_cannot_be_four :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalGaugeFixedHolonomyMeasure.Probes
