/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactOrientedMeasuredSurface

/-!
# Hostile probes for compact oriented measured surfaces
-/

namespace YangMills.Geometry.CompactOrientedMeasuredSurface.Probes

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

universe uE uH uSurface

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type uH} [TopologicalSpace H]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [MeasurableSpace Surface] [BorelSpace Surface]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H Surface] [IsManifold I ∞ Surface]
    [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface]

/-- The exact manifold model is genuinely two-dimensional. -/
theorem exact_dimension_two
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    Module.finrank ℝ E = 2 :=
  surface.model_finrank_two

/-- A dimension-confused model cannot pass the surface contract. -/
theorem wrong_dimension_blocked
    (surface : CompactOrientedMeasuredSurfaceData I Surface)
    (wrong : Module.finrank ℝ E ≠ 2) : False :=
  wrong surface.model_finrank_two

/-- Connectedness is attached to the exact full carrier and supplies an actual point. -/
theorem exact_connected_nonempty
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    IsConnected (Set.univ : Set Surface) ∧ Nonempty Surface :=
  ⟨surface.connected, surface.surface_nonempty⟩

/-- The selected orientation is represented by one smooth top form on the same manifold. -/
def exact_orientation
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    YangMills.Mathematics.SmoothManifoldDifferentialForm
      I Surface ℝ (ContinuousLinearEquiv.refl ℝ ℝ) 2 :=
  surface.orientationForm

/-- The orientation form cannot collapse at any point. -/
theorem zero_orientation_at_point_blocked
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (point : Surface)
    (claimed : surface.orientationForm.toForm point = 0) : False :=
  surface.exact_orientation_nonzero point claimed

/-- The exact area carrier is finite, positive, real-positive, and nonzero. -/
theorem exact_area_nondegenerate
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    surface.areaMeasure Set.univ ≠ (⊤ : ENNReal) ∧
      0 < surface.areaMeasure Set.univ ∧
      0 < surface.totalArea ∧ surface.areaMeasure ≠ 0 :=
  ⟨surface.areaMeasure_ne_top, surface.areaMeasure_pos,
    surface.totalArea_pos, surface.areaMeasure_ne_zero⟩

/-- Every chart density is measurable globally, smooth on the exact chart target, and strictly
positive there. -/
theorem exact_positive_smooth_chart_density
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface) :
    Measurable (surface.coordinateDensity center) ∧
      ContDiffOn ℝ ∞ (surface.coordinateDensity center) (extChartAt I center).target ∧
      ∀ coordinate ∈ (extChartAt I center).target,
        0 < surface.coordinateDensity center coordinate :=
  ⟨surface.coordinateDensity_measurable center,
    surface.coordinateDensity_smoothOn center,
    surface.coordinateDensity_pos center⟩

/-- The chart pushforward uses an actually a.e.-measurable extended chart on the restricted source,
preventing `Measure.map` from silently becoming zero. -/
theorem exact_chart_aemeasurable
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface) :
    AEMeasurable (extChartAt I center)
      (surface.areaMeasure.restrict (extChartAt I center).source) :=
  surface.chart_aemeasurable center

/-- Every chart sees the same designated surface measure through its exact positive density. -/
theorem exact_chart_measure
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface) :
    Measure.map (extChartAt I center)
        (surface.areaMeasure.restrict (extChartAt I center).source) =
      (Measure.addHaar.restrict (extChartAt I center).target).withDensity
        (fun coordinate => ENNReal.ofReal (surface.coordinateDensity center coordinate)) :=
  surface.exact_chart_measure center

/-- An unrelated proposed chart measure is rejected. -/
theorem unrelated_chart_measure_blocked
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface)
    (wrong : Measure E)
    (different : wrong ≠
      (Measure.addHaar.restrict (extChartAt I center).target).withDensity
        (fun coordinate => ENNReal.ofReal (surface.coordinateDensity center coordinate)))
    (claimed : Measure.map (extChartAt I center)
      (surface.areaMeasure.restrict (extChartAt I center).source) = wrong) : False := by
  apply different
  rw [← claimed]
  exact surface.exact_chart_measure center

/-- Boundary-component labels are definitionally the connected-component quotient of Mathlib's
actual manifold boundary subtype. -/
theorem exact_boundary_component_carrier
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    surface.BoundaryComponent = ConnectedComponents (I.boundary Surface) :=
  rfl

/-- Mathlib's actual boundary set is closed and compact; no auxiliary boundary carrier substitutes
for it. -/
theorem exact_boundary_compact
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    IsClosed (I.boundary Surface) ∧ IsCompact (I.boundary Surface) :=
  ⟨surface.boundary_isClosed, surface.boundary_isCompact⟩

end YangMills.Geometry.CompactOrientedMeasuredSurface.Probes
