/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Connected.Clopen

/-!
# Compact oriented measured surfaces

This file packages the exact intrinsic surface nucleus used by compact-surface Yang--Mills
constructions: a genuine two-dimensional smooth manifold with corners, compactness, connectedness, a
chosen orientation represented by a nowhere-vanishing smooth top form, and a finite positive Borel
measure with positive smooth density in every exact extended chart.

The chart-density carrier uses the additive Haar/Lebesgue measure on the finite-dimensional model.
Its normalization is immaterial because the positive density changes inversely. Boundary components,
when later needed, are indexed by the actual connected components of Mathlib's exact manifold
boundary set. Pinned Mathlib does not yet make that boundary subtype a general smooth submanifold;
circle presentations and orientation-reversing boundary diffeomorphisms therefore remain a separate
layer.

No surface, boundary presentation, probability law, or Yang--Mills model is constructed here.
-/

namespace YangMills.Geometry

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

universe uE uH uSurface

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type uH} [TopologicalSpace H]
    {Surface : Type uSurface} [TopologicalSpace Surface]
    [MeasurableSpace Surface] [BorelSpace Surface]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H Surface] [IsManifold I ∞ Surface]
    [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface]

/-- Exact compact-oriented-measured surface nucleus. A nowhere-zero smooth real two-form is used as
a concrete orientation representative because pinned Mathlib has no manifold-orientation bundle.
The area measure is not claimed to be metric-induced. -/
structure CompactOrientedMeasuredSurfaceData
    (I : ModelWithCorners ℝ E H) (Surface : Type uSurface)
    [TopologicalSpace Surface] [MeasurableSpace Surface] [BorelSpace Surface]
    [ChartedSpace H Surface] [IsManifold I ∞ Surface]
    [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] where
  /-- The manifold model has exact real dimension two. -/
  model_finrank_two : Module.finrank ℝ E = 2
  /-- The whole exact carrier is connected and nonempty. -/
  connected : IsConnected (Set.univ : Set Surface)
  /-- A smooth nowhere-vanishing top form selecting one orientation. -/
  orientationForm : YangMills.Mathematics.SmoothManifoldDifferentialForm
    I Surface ℝ (ContinuousLinearEquiv.refl ℝ ℝ) 2
  orientationForm_ne_zero : ∀ point, orientationForm.toForm point ≠ 0
  /-- Designated Lebesguian area measure on the exact surface carrier. -/
  areaMeasure : Measure Surface
  areaMeasure_ne_top : areaMeasure Set.univ ≠ (⊤ : ENNReal)
  areaMeasure_pos : 0 < areaMeasure Set.univ
  /-- Positive smooth chart density relative to additive Haar/Lebesgue measure on the model. Values
  outside the exact chart target are irrelevant but retained measurably to avoid a vacuous
  nonmeasurable `Measure.map`. -/
  coordinateDensity : Surface → E → ℝ
  coordinateDensity_measurable : ∀ center, Measurable (coordinateDensity center)
  coordinateDensity_smoothOn : ∀ center,
    ContDiffOn ℝ ∞ (coordinateDensity center) (extChartAt I center).target
  coordinateDensity_pos : ∀ center coordinate,
    coordinate ∈ (extChartAt I center).target → 0 < coordinateDensity center coordinate
  chart_aemeasurable : ∀ center,
    AEMeasurable (extChartAt I center)
      (areaMeasure.restrict (extChartAt I center).source)
  /-- Exact local density identity in every extended chart. -/
  areaMeasure_chart : ∀ center,
    Measure.map (extChartAt I center)
        (areaMeasure.restrict (extChartAt I center).source) =
      (Measure.addHaar.restrict (extChartAt I center).target).withDensity
        (fun coordinate => ENNReal.ofReal (coordinateDensity center coordinate))

namespace CompactOrientedMeasuredSurfaceData

/-- The exact topological boundary-component carrier. No smooth boundary-submanifold structure is
silently inferred. -/
def BoundaryComponent
    (_surface : CompactOrientedMeasuredSurfaceData I Surface) : Type uSurface :=
  ConnectedComponents (I.boundary Surface)

/-- Connectedness of the full carrier supplies an actual surface point. -/
theorem surface_nonempty
    (surface : CompactOrientedMeasuredSurfaceData I Surface) : Nonempty Surface :=
  ⟨surface.connected.nonempty.choose⟩

/-- The designated area measure is nonzero. -/
theorem areaMeasure_ne_zero
    (surface : CompactOrientedMeasuredSurfaceData I Surface) : surface.areaMeasure ≠ 0 := by
  intro zero
  have positive := surface.areaMeasure_pos
  rw [zero] at positive
  simp at positive

/-- Exact finite positive real total area. -/
def totalArea (surface : CompactOrientedMeasuredSurfaceData I Surface) : ℝ :=
  (surface.areaMeasure Set.univ).toReal

/-- The real total area is strictly positive. -/
theorem totalArea_pos
    (surface : CompactOrientedMeasuredSurfaceData I Surface) : 0 < surface.totalArea :=
  ENNReal.toReal_pos (ne_of_gt surface.areaMeasure_pos) surface.areaMeasure_ne_top

/-- Mathlib's exact manifold boundary is closed. -/
theorem boundary_isClosed
    (_surface : CompactOrientedMeasuredSurfaceData I Surface) :
    IsClosed (I.boundary Surface) :=
  I.isClosed_boundary (n := (∞ : WithTop ℕ∞)) (by simp)

/-- Consequently the exact boundary subtype is compact, including the empty-boundary case. -/
theorem boundary_isCompact
    (surface : CompactOrientedMeasuredSurfaceData I Surface) :
    IsCompact (I.boundary Surface) :=
  surface.boundary_isClosed.isCompact

/-- Every orientation value is genuinely nonzero on the exact tangent fiber. -/
theorem exact_orientation_nonzero
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (point : Surface) :
    surface.orientationForm.toForm point ≠ 0 :=
  surface.orientationForm_ne_zero point

/-- The exact chart law cannot be replaced by an unrelated local measure. -/
theorem exact_chart_measure
    (surface : CompactOrientedMeasuredSurfaceData I Surface) (center : Surface) :
    Measure.map (extChartAt I center)
        (surface.areaMeasure.restrict (extChartAt I center).source) =
      (Measure.addHaar.restrict (extChartAt I center).target).withDensity
        (fun coordinate => ENNReal.ofReal (surface.coordinateDensity center coordinate)) :=
  surface.areaMeasure_chart center

end CompactOrientedMeasuredSurfaceData

end

end YangMills.Geometry
