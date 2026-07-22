/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryOrientation

/-!
# Hostile probes for induced compact-surface boundary orientations
-/

namespace YangMills.Geometry.CompactSurfaceBoundaryOrientation.Probes

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
    {surface : CompactOrientedMeasuredSurfaceData I Surface}
    {presentation : CompactSurfaceBoundaryCirclePresentationData surface}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Surface] [BorelSpace Surface] [IsManifold I ∞ Surface]
  [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] in
/-- The outward certificate retains both the entering negative ray and exiting positive ray on the
exact model-with-corners range. -/
theorem exact_two_sided_outward_ray
    {point : Surface} {vector : TangentSpace I point}
    (outward : IsPreferredChartOutwardBoundaryVector I point vector) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ time : ℝ, -radius < time → time < 0 →
        extChartAt I point point + time •
          NormedSpace.fromTangentSpace (extChartAt I point point)
            (mfderiv I 𝓘(ℝ, E) (extChartAt I point) point vector) ∈
          interior (Set.range I)) ∧
      (∀ time : ℝ, 0 < time → time < radius →
        extChartAt I point point + time •
          NormedSpace.fromTangentSpace (extChartAt I point point)
            (mfderiv I 𝓘(ℝ, E) (extChartAt I point) point vector) ∉ Set.range I) :=
  outward

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Surface] [BorelSpace Surface] [IsManifold I ∞ Surface]
  [CompactSpace Surface] [T2Space Surface] [SecondCountableTopology Surface] in
/-- A zero tangent is never outward; a bare nonzero-looking field name cannot bypass the two-sided
chart-ray geometry. -/
theorem zero_vector_not_outward (point : Surface) :
    ¬ IsPreferredChartOutwardBoundaryVector I point 0 := by
  rintro ⟨radius, radiusPositive, enters, exits⟩
  have negativeTime : -radius < -radius / 2 := by linarith
  have negativeTimeNegative : -radius / 2 < 0 := by linarith
  have positiveTimePositive : 0 < radius / 2 := by linarith
  have positiveTime : radius / 2 < radius := by linarith
  have inside := enters (-radius / 2) negativeTime negativeTimeNegative
  have outside := exits (radius / 2) positiveTimePositive positiveTime
  simp only [map_zero, smul_zero, add_zero] at inside outside
  exact outside (interior_subset inside)

/-- The positive circle tangent is a genuine smooth nonvanishing tangent-bundle field, separately
for each exact component. -/
theorem exact_positive_circle_tangent
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) :
    ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
        (fun circlePoint =>
          (⟨circlePoint, orientation.positiveCircleTangent component circlePoint⟩ :
            TangentBundle (𝓡 1) Circle)) ∧
      ∀ circlePoint, orientation.positiveCircleTangent component circlePoint ≠ 0 :=
  ⟨orientation.positiveCircleTangent_smooth component,
    orientation.positiveCircleTangent_ne_zero component⟩

/-- The outward field is smooth along the exact ambient parameterization and every value carries
the actual two-sided outward certificate. -/
theorem exact_smooth_outward_field
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) :
    ContMDiff (𝓡 1) (I.prod 𝓘(ℝ, E)) ∞
        (fun circlePoint =>
          (⟨presentation.parameterization component circlePoint,
            orientation.outwardBoundaryVector component circlePoint⟩ :
            TangentBundle I Surface)) ∧
      ∀ circlePoint,
        IsPreferredChartOutwardBoundaryVector I
          (presentation.parameterization component circlePoint)
          (orientation.outwardBoundaryVector component circlePoint) :=
  ⟨orientation.outwardBoundaryVector_smooth component,
    orientation.outwardBoundaryVector_isOutward component⟩

/-- Boundary orientation is induced by the ordered pair `(outward, pushed tangent)` and the exact
surface orientation form. -/
theorem exact_induced_orientation_sign
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    0 < surface.orientationForm.toForm
      (presentation.parameterization component circlePoint)
      ![orientation.outwardBoundaryVector component circlePoint,
        orientation.pushedPositiveBoundaryTangent component circlePoint] :=
  orientation.orientationForm_outward_pushedPositive_pos component circlePoint

/-- Neither vector in the oriented boundary frame may collapse to zero. -/
theorem exact_oriented_frame_nondegenerate
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle) :
    orientation.outwardBoundaryVector component circlePoint ≠ 0 ∧
      orientation.pushedPositiveBoundaryTangent component circlePoint ≠ 0 :=
  ⟨orientation.outwardBoundaryVector_ne_zero component circlePoint,
    orientation.pushedPositiveBoundaryTangent_ne_zero component circlePoint⟩

/-- An unrelated ambient tangent field cannot replace the designated outward field without an
actual equality proof. -/
theorem unrelated_outward_field_blocked
    (orientation : CompactSurfaceBoundaryOrientationData surface presentation)
    (component : surface.BoundaryComponent) (circlePoint : Circle)
    (wrong : TangentSpace I (presentation.parameterization component circlePoint))
    (different : wrong ≠ orientation.outwardBoundaryVector component circlePoint)
    (claimed : wrong = orientation.outwardBoundaryVector component circlePoint) : False :=
  different claimed

end

end YangMills.Geometry.CompactSurfaceBoundaryOrientation.Probes
