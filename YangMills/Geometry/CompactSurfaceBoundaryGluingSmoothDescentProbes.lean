/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryGluingSmoothDescent

/-!
# Hostile probes for smooth compact-surface gluing descent
-/

namespace YangMills.Geometry.CompactSurfaceBoundaryGluingSmoothDescent.Probes

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uEG uHG

variable
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL] {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER] {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : CompactSurfaceBoundaryOrientationData leftSurface leftPresentation}
    {rightSurface : CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : CompactSurfaceBoundaryOrientationData rightSurface rightPresentation}
    {identification : CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [MeasurableSpace EG] [BorelSpace EG] {HG : Type uHG} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG (GluedSurfaceCarrier (identification := identification))]
    [IsManifold IG ∞ (GluedSurfaceCarrier (identification := identification))]

/-- The descended carrier is genuinely another exact two-dimensional compact oriented measured
surface, not merely the pre-existing quotient type. -/
theorem exact_glued_surface_nucleus
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Module.finrank ℝ EG = 2 ∧
      0 < descent.gluedSurface.areaMeasure Set.univ :=
  ⟨descent.glued_model_finrank_two, descent.gluedSurface.areaMeasure_pos⟩

/-- Descent supplies only the differential immersion obligations; exact topological embeddings were
already derived from the quotient construction. -/
theorem exact_side_immersion_obligations
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Manifold.IsImmersion IL IG ∞
        (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Manifold.IsImmersion IR IG ∞
        (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) :=
  ⟨descent.left_immersion, descent.right_immersion⟩

/-- Both whole-side maps are derived genuine smooth embeddings into the same descended manifold. -/
theorem exact_side_smooth_embeddings
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Manifold.IsSmoothEmbedding IL IG ∞
        (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Manifold.IsSmoothEmbedding IR IG ∞
        (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) ∧
      Measurable (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Measurable (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) :=
  ⟨descent.left_smoothEmbedding, descent.right_smoothEmbedding,
    descent.sideInclusions_measurable.1, descent.sideInclusions_measurable.2⟩

/-- Both glued pullbacks represent exactly the original side orientations through explicit
strictly positive scales; neither side may be omitted or orientation-reversed. -/
theorem exact_both_orientation_pullbacks
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))
    (leftPoint : SL) (leftVectors : Fin 2 → TangentSpace IL leftPoint)
    (rightPoint : SR) (rightVectors : Fin 2 → TangentSpace IR rightPoint) :
    (0 < descent.left_orientationScale leftPoint ∧
      descent.gluedSurface.orientationForm.toForm
          (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification leftPoint)
          (fun index => mfderiv IL IG
            (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) leftPoint
            (leftVectors index)) =
        descent.left_orientationScale leftPoint *
          leftSurface.orientationForm.toForm leftPoint leftVectors) ∧
    (0 < descent.right_orientationScale rightPoint ∧
      descent.gluedSurface.orientationForm.toForm
          (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification rightPoint)
          (fun index => mfderiv IR IG
            (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) rightPoint
            (rightVectors index)) =
        descent.right_orientationScale rightPoint *
          rightSurface.orientationForm.toForm rightPoint rightVectors) :=
  ⟨⟨descent.left_orientationScale_pos leftPoint,
      descent.left_orientation_pullback leftPoint leftVectors⟩,
    ⟨descent.right_orientationScale_pos rightPoint,
      descent.right_orientation_pullback rightPoint rightVectors⟩⟩

/-- Area descent is the exact sum of pushforwards and both original boundaries are null. -/
theorem exact_area_descent
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    leftSurface.areaMeasure (IL.boundary SL) = 0 ∧
      rightSurface.areaMeasure (IR.boundary SR) = 0 ∧
      descent.gluedSurface.areaMeasure =
        Measure.map (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
            leftSurface.areaMeasure +
          Measure.map (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
            rightSurface.areaMeasure :=
  ⟨descent.left_boundary_null, descent.right_boundary_null,
    descent.areaMeasure_eq_sum_pushforward⟩

/-- Exactly unselected boundary images remain, while every selected seam is interior. -/
theorem exact_boundary_and_seam
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    IG.boundary (GluedSurfaceCarrier (identification := identification)) =
        CompactSurfaceBoundaryGluingQuotient.leftInclusion identification ''
            (IL.boundary SL \ selectedLeftBoundarySet (identification := identification)) ∪
          CompactSurfaceBoundaryGluingQuotient.rightInclusion identification ''
            (IR.boundary SR \ selectedRightBoundarySet (identification := identification)) ∧
      CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
          (identification.leftBoundaryPoint pair circlePoint) ∈
        IG.interior (GluedSurfaceCarrier (identification := identification)) ∧
      CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
          (identification.leftBoundaryPoint pair circlePoint) ∉
        IG.boundary (GluedSurfaceCarrier (identification := identification)) :=
  ⟨descent.boundary_eq_unselected_images,
    descent.seam_mem_interior pair circlePoint,
    descent.seam_not_mem_boundary pair circlePoint⟩

/-- An unrelated candidate area measure cannot replace the exact sum pushforward. -/
theorem unrelated_glued_area_blocked
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))
    (wrong : Measure (GluedSurfaceCarrier (identification := identification)))
    (different : wrong ≠
      Measure.map (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
          leftSurface.areaMeasure +
        Measure.map (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
          rightSurface.areaMeasure)
    (claimed : descent.gluedSurface.areaMeasure = wrong) : False := by
  apply different
  rw [← claimed]
  exact descent.areaMeasure_eq_sum_pushforward

end

end YangMills.Geometry.CompactSurfaceBoundaryGluingSmoothDescent.Probes
