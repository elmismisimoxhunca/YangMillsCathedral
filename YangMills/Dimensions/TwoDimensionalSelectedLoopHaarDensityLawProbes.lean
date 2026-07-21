/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopHaarDensityLaw

/-!
# Hostile probes for the selected two-dimensional loop Haar-density law

The probes reject nonclosed and zero-area replacements, a zero density measure, changed sampled
holonomy laws, noncentral/inversion-asymmetric density substitutions, a disconnected observable
interpretation, and a wrong expectation value. No loop, density, heat kernel, or measure is
constructed.
-/

namespace YangMills.Dimensions.TwoDimensionalSelectedLoopHaarDensityLaw.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

variable {G Gauge Sample Connection : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [Group Gauge] [MeasurableSpace Sample]
  {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}

/-- The selected source-facing loop is exactly closed. -/
theorem exact_selected_loop_closed
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) :
    base.pathSource law.selectedLoop = base.pathTarget law.selectedLoop :=
  law.selectedLoop_closed

/-- Closedness and the exact ambient action expose conjugation by one endpoint value. -/
theorem exact_selected_loop_gauge_conjugation
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (g : Gauge) (A : Connection) :
    base.holonomy law.selectedLoop (base.gaugeAction g A) =
      base.gaugeValue g (base.pathSource law.selectedLoop) *
        base.holonomy law.selectedLoop A *
          (base.gaugeValue g (base.pathSource law.selectedLoop))⁻¹ :=
  law.selectedLoop_holonomy_gauge_conjugation g A

/-- A nonpositive area cannot replace the selected positive enclosed area. -/
theorem nonpositive_area_blocked
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (claimed : law.enclosedArea ≤ 0) : False :=
  (not_le_of_gt law.enclosedArea_pos) claimed

/-- The exact selected density measure is normalized and cannot be zero. -/
theorem zero_density_measure_blocked
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (claimed : (normalizedCompactHaarMeasure G).withDensity
      (law.selectedAreaDensity law.enclosedArea) = 0) : False :=
  law.densityMeasure_ne_zero claimed

/-- The pushforward uses the exact sampled holonomy and exact gauge-fixed probability law. -/
theorem exact_selected_sampled_holonomy_law
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) :
    Measure.map
        (fun ω => base.holonomy law.selectedLoop (base.sampleConnection ω))
        base.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity law.enclosedArea) :=
  law.selectedLoop_law

/-- A changed pushforward measure is rejected. -/
theorem changed_selected_loop_law_blocked
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (wrong : Measure G)
    (different : wrong ≠
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity law.enclosedArea))
    (claimed : Measure.map
      (fun ω => base.holonomy law.selectedLoop (base.sampleConnection ω))
      base.probabilityMeasure = wrong) : False := by
  apply different
  rw [← claimed]
  exact law.selectedLoop_law

/-- Centrality is required at the exact positive selected area. -/
theorem exact_selected_density_central
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) (h g : G) :
    law.selectedAreaDensity law.enclosedArea (h * g * h⁻¹) =
      law.selectedAreaDensity law.enclosedArea g :=
  law.selectedAreaDensity_central law.enclosedArea law.enclosedArea_pos h g

/-- Inversion symmetry is required at the exact positive selected area. -/
theorem exact_selected_density_inv
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) (g : G) :
    law.selectedAreaDensity law.enclosedArea g⁻¹ =
      law.selectedAreaDensity law.enclosedArea g :=
  law.selectedAreaDensity_inv law.enclosedArea law.enclosedArea_pos g

/-- The physical observable is tied to the same selected ambient holonomy. -/
theorem exact_physical_observable_interpretation
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base) (A : Connection) :
    base.observable law.physicalObservable A =
      law.loopClassFunction (base.holonomy law.selectedLoop A) :=
  law.physicalObservable_eq_loopClassFunction A

/-- A wrong selected expectation contradicts the derived selected Haar-density measure formula. -/
theorem wrong_selected_expectation_blocked
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (wrong : ℂ)
    (different : wrong ≠
      ∫ g, law.loopClassFunction g
        ∂((normalizedCompactHaarMeasure G).withDensity
          (law.selectedAreaDensity law.enclosedArea)))
    (claimed : base.expectation law.physicalObservable = wrong) : False := by
  apply different
  rw [← claimed]
  exact law.physicalObservable_expectation_eq_selectedHaarDensityMeasure

/-- The source-specific lower-dimensional law cannot be substituted for the Clay endpoint. -/
theorem selected_loop_law_cannot_be_four :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSelectedLoopHaarDensityLaw.Probes
