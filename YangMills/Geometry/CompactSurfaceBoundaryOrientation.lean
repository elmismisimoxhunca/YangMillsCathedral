/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryCirclePresentation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Induced orientations on exact compact-surface boundary circles

This file supplies the next source-facing layer after exact boundary-circle presentations. Because
pinned Mathlib does not install the boundary of a general manifold with corners as a smooth
submanifold, an outward direction is not represented by an unconstrained field name. Instead it is
certified in the preferred extended chart: a short negative ray enters the interior of the exact
model-with-corners range and the corresponding positive ray exits that range.

A nonzero smooth tangent field orients each presented circle. Its pushed tangent is declared
positive precisely when the selected surface orientation form evaluates positively on the ordered
pair `(outward direction, boundary tangent)`. This is the standard boundary-orientation convention.
No metric normal, collar theorem, gluing, or Yang--Mills law is constructed here. Chart-independence
of the outward-ray predicate remains a separate mathematical obligation.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

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

/-- A tangent direction whose preferred extended-chart ray genuinely crosses out of the exact
model-with-corners range. The negative ray must lie in the interior, while the positive ray must
lie outside the range. Both conditions are required; an arbitrary nonzero tangent cannot serve as
an outward direction. -/
def IsPreferredChartOutwardBoundaryVector
    (I : ModelWithCorners ℝ E H) {Surface : Type uSurface} [TopologicalSpace Surface]
    [ChartedSpace H Surface] (point : Surface) (vector : TangentSpace I point) : Prop :=
  let coordinate : E := extChartAt I point point
  let coordinateVector : E := NormedSpace.fromTangentSpace coordinate
    (mfderiv I 𝓘(ℝ, E) (extChartAt I point) point vector)
  ∃ radius : ℝ, 0 < radius ∧
    (∀ time : ℝ, -radius < time → time < 0 →
      coordinate + time • coordinateVector ∈ interior (Set.range I)) ∧
    (∀ time : ℝ, 0 < time → time < radius →
      coordinate + time • coordinateVector ∉ Set.range I)

/-- Source-facing induced orientation data for every exact boundary circle. Smooth tangent and
outward fields are retained as actual tangent-bundle maps. -/
structure CompactSurfaceBoundaryOrientationData
    (surface : CompactOrientedMeasuredSurfaceData I Surface)
    (presentation : CompactSurfaceBoundaryCirclePresentationData surface) where
  /-- A component-indexed positive tangent field on its circle parameterization. -/
  positiveCircleTangent : ∀ (_component : surface.BoundaryComponent) (circlePoint : Circle),
    TangentSpace (𝓡 1) circlePoint
  positiveCircleTangent_smooth : ∀ component,
    ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      (fun circlePoint =>
        (⟨circlePoint, positiveCircleTangent component circlePoint⟩ :
          TangentBundle (𝓡 1) Circle))
  positiveCircleTangent_ne_zero : ∀ component circlePoint,
    positiveCircleTangent component circlePoint ≠ 0
  /-- A smooth tangent field along each ambient boundary parameterization. -/
  outwardBoundaryVector : ∀ component circlePoint,
    TangentSpace I (presentation.parameterization component circlePoint)
  outwardBoundaryVector_smooth : ∀ component,
    ContMDiff (𝓡 1) (I.prod 𝓘(ℝ, E)) ∞
      (fun circlePoint =>
        (⟨presentation.parameterization component circlePoint,
          outwardBoundaryVector component circlePoint⟩ : TangentBundle I Surface))
  /-- The field is genuinely outward in the exact preferred-chart ray sense above. -/
  outwardBoundaryVector_isOutward : ∀ component circlePoint,
    IsPreferredChartOutwardBoundaryVector I
      (presentation.parameterization component circlePoint)
      (outwardBoundaryVector component circlePoint)
  /-- The pushed circle tangent has the orientation induced by putting the outward direction first
  in the selected surface orientation. -/
  inducedOrientation_positive : ∀ component circlePoint,
    0 < surface.orientationForm.toForm
      (presentation.parameterization component circlePoint)
      ![outwardBoundaryVector component circlePoint,
        mfderiv (𝓡 1) I (presentation.parameterization component) circlePoint
          (positiveCircleTangent component circlePoint)]

namespace CompactSurfaceBoundaryOrientationData

variable
    {surface : CompactOrientedMeasuredSurfaceData I Surface}
    {presentation : CompactSurfaceBoundaryCirclePresentationData surface}

/-- The exact ambient tangent obtained by differentiating a boundary-circle parameterization. -/
def pushedPositiveBoundaryTangent
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    TangentSpace I (presentation.parameterization component circlePoint) :=
  mfderiv (𝓡 1) I (presentation.parameterization component) circlePoint
    (orientation.positiveCircleTangent component circlePoint)

/-- The induced-orientation equation exposed through the named pushed tangent. -/
theorem orientationForm_outward_pushedPositive_pos
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    0 < surface.orientationForm.toForm
      (presentation.parameterization component circlePoint)
      ![orientation.outwardBoundaryVector component circlePoint,
        orientation.pushedPositiveBoundaryTangent component circlePoint] :=
  orientation.inducedOrientation_positive component circlePoint

/-- The outward vector cannot collapse to zero: positivity of the alternating orientation form
already forbids that collapse. -/
theorem outwardBoundaryVector_ne_zero
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    orientation.outwardBoundaryVector component circlePoint ≠ 0 := by
  intro zero
  have positive := orientation.orientationForm_outward_pushedPositive_pos component circlePoint
  rw [zero] at positive
  have evaluationZero :
      surface.orientationForm.toForm
        (presentation.parameterization component circlePoint)
        ![0, orientation.pushedPositiveBoundaryTangent component circlePoint] = 0 :=
    (surface.orientationForm.toForm
      (presentation.parameterization component circlePoint)).map_coord_zero 0 (by simp)
  rw [evaluationZero] at positive
  exact (lt_irrefl 0 positive)

/-- The pushed positive boundary tangent cannot collapse to zero. -/
theorem pushedPositiveBoundaryTangent_ne_zero
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    orientation.pushedPositiveBoundaryTangent component circlePoint ≠ 0 := by
  intro zero
  have positive := orientation.orientationForm_outward_pushedPositive_pos component circlePoint
  rw [zero] at positive
  have evaluationZero :
      surface.orientationForm.toForm
        (presentation.parameterization component circlePoint)
        ![orientation.outwardBoundaryVector component circlePoint, 0] = 0 :=
    (surface.orientationForm.toForm
      (presentation.parameterization component circlePoint)).map_coord_zero 1 (by simp)
  rw [evaluationZero] at positive
  exact (lt_irrefl 0 positive)

end CompactSurfaceBoundaryOrientationData

end

end YangMills.Geometry
