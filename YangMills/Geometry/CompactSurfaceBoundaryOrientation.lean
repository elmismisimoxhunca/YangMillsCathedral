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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Surface] [BorelSpace Surface] [IsManifold I ∞ Surface]
  [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] in
/-- Positive rescaling preserves the exact preferred-chart outward-ray certificate. -/
theorem IsPreferredChartOutwardBoundaryVector.smul_of_pos
    {point : Surface} {vector : TangentSpace I point} {scale : ℝ}
    (outward : IsPreferredChartOutwardBoundaryVector I point vector)
    (scale_pos : 0 < scale) :
    IsPreferredChartOutwardBoundaryVector I point (scale • vector) := by
  rw [IsPreferredChartOutwardBoundaryVector] at outward ⊢
  rcases outward with ⟨radius, radius_pos, entersInterior, exitsRange⟩
  refine ⟨radius / scale, div_pos radius_pos scale_pos, ?_, ?_⟩
  · intro time lower upper
    have lower' : -radius / scale < time := by
      simpa only [neg_div] using lower
    have rescaled_lower : -radius < time * scale :=
      (div_lt_iff₀ scale_pos).mp lower'
    have rescaled_upper : time * scale < 0 :=
      mul_neg_of_neg_of_pos upper scale_pos
    simpa only [map_smul, smul_smul] using
      entersInterior (time * scale) rescaled_lower rescaled_upper
  · intro time lower upper
    have rescaled_lower : 0 < time * scale := mul_pos lower scale_pos
    have rescaled_upper : time * scale < radius :=
      (lt_div_iff₀ scale_pos).mp upper
    simpa only [map_smul, smul_smul] using
      exitsRange (time * scale) rescaled_lower rescaled_upper

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Surface] [BorelSpace Surface] [IsManifold I ∞ Surface]
  [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] in
/-- Preferred-chart outwardness depends only on the positively oriented tangent ray. -/
theorem isPreferredChartOutwardBoundaryVector_smul_iff
    {point : Surface} {vector : TangentSpace I point} {scale : ℝ}
    (scale_pos : 0 < scale) :
    IsPreferredChartOutwardBoundaryVector I point (scale • vector) ↔
      IsPreferredChartOutwardBoundaryVector I point vector := by
  constructor
  · intro outward
    have rescaled := outward.smul_of_pos (inv_pos.mpr scale_pos)
    simpa [smul_smul, ne_of_gt scale_pos] using rescaled
  · intro outward
    exact outward.smul_of_pos scale_pos

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Surface] [BorelSpace Surface] [IsManifold I ∞ Surface]
  [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] in
/-- The zero tangent vector cannot satisfy the positive-ray exit clause. -/
theorem not_isPreferredChartOutwardBoundaryVector_zero (point : Surface) :
    ¬ IsPreferredChartOutwardBoundaryVector I point (0 : TangentSpace I point) := by
  rw [IsPreferredChartOutwardBoundaryVector]
  rintro ⟨radius, radius_pos, _entersInterior, exitsRange⟩
  have exitsAtHalf :=
    exitsRange (radius / 2) (half_pos radius_pos) (half_lt_self radius_pos)
  simp only [map_zero, smul_zero, add_zero] at exitsAtHalf
  exact exitsAtHalf
    (extChartAt_target_subset_range point (mem_extChartAt_target point))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Surface] [BorelSpace Surface] [IsManifold I ∞ Surface]
  [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] in
/-- Every preferred-chart outward vector is nonzero. -/
theorem IsPreferredChartOutwardBoundaryVector.ne_zero
    {point : Surface} {vector : TangentSpace I point}
    (outward : IsPreferredChartOutwardBoundaryVector I point vector) : vector ≠ 0 := by
  intro vector_zero
  subst vector
  exact not_isPreferredChartOutwardBoundaryVector_zero (I := I) point outward

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

/-- The outward vector cannot collapse to zero; this follows already from its exact positive-ray
exit certificate, independently of the selected orientation form. -/
theorem outwardBoundaryVector_ne_zero
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    orientation.outwardBoundaryVector component circlePoint ≠ 0 :=
  (orientation.outwardBoundaryVector_isOutward component circlePoint).ne_zero

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
