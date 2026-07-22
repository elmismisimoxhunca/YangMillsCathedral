/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient
import YangMills.Geometry.CompactOrientedMeasuredSurfaceBoundaryNull

/-!
# Canonical area measure on a compact-surface gluing quotient

The area candidate on the already constructed quotient is the sum of the pushforwards of the two
designated side measures. It is finite, strictly positive, and nonzero before any descended smooth
manifold or orientation is supplied.
-/

namespace YangMills.Geometry

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR

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

/-- Canonical area candidate on the exact glued quotient. -/
def compactSurfaceBoundaryGluedAreaMeasure :
    Measure (CompactSurfaceBoundaryGluingQuotient identification) :=
  Measure.map (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
      leftSurface.areaMeasure +
    Measure.map (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
      rightSurface.areaMeasure

/-- Total glued area is exactly the sum of the two side areas. -/
theorem compactSurfaceBoundaryGluedAreaMeasure_univ :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification) Set.univ =
      leftSurface.areaMeasure Set.univ + rightSurface.areaMeasure Set.univ := by
  rw [compactSurfaceBoundaryGluedAreaMeasure, Measure.add_apply,
    Measure.map_apply_of_aemeasurable
      ((CompactSurfaceBoundaryGluingQuotient.sideInclusions_measurable identification).1.aemeasurable)
      MeasurableSet.univ,
    Measure.map_apply_of_aemeasurable
      ((CompactSurfaceBoundaryGluingQuotient.sideInclusions_measurable identification).2.aemeasurable)
      MeasurableSet.univ]
  simp

/-- The canonical glued area is finite. -/
theorem compactSurfaceBoundaryGluedAreaMeasure_ne_top :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification) Set.univ ≠ ⊤ := by
  rw [compactSurfaceBoundaryGluedAreaMeasure_univ]
  exact ENNReal.add_ne_top.mpr
    ⟨leftSurface.areaMeasure_ne_top, rightSurface.areaMeasure_ne_top⟩

/-- The canonical glued area is strictly positive. -/
theorem compactSurfaceBoundaryGluedAreaMeasure_pos :
    0 < compactSurfaceBoundaryGluedAreaMeasure (identification := identification) Set.univ := by
  rw [compactSurfaceBoundaryGluedAreaMeasure_univ]
  exact lt_of_lt_of_le leftSurface.areaMeasure_pos (le_add_right (le_refl _))

/-- The canonical glued measure is not the zero measure. -/
theorem compactSurfaceBoundaryGluedAreaMeasure_ne_zero :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification) ≠ 0 := by
  intro zero
  have positive := compactSurfaceBoundaryGluedAreaMeasure_pos (identification := identification)
  rw [zero] at positive
  simp at positive

/-- Exact seam subset of the glued quotient, represented from the left selected boundary circles. -/
def compactSurfaceBoundaryGluingSeam :
    Set (CompactSurfaceBoundaryGluingQuotient identification) :=
  ⋃ pair : Fin identification.pairCount,
    Set.range (fun circlePoint =>
      CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint))

/-- The exact seam is compact and therefore Borel measurable. -/
theorem compactSurfaceBoundaryGluingSeam_isCompact :
    IsCompact (compactSurfaceBoundaryGluingSeam (identification := identification)) := by
  apply isCompact_iUnion
  intro pair
  apply isCompact_range
  exact (CompactSurfaceBoundaryGluingQuotient.leftInclusion_continuous identification).comp
    (leftPresentation.parameterization_smoothEmbedding
      (identification.leftComponent pair)).contMDiff.continuous

/-- The exact seam has zero canonical glued area. Both pushforward terms vanish because their
preimages lie in the already derived null side boundaries. -/
theorem compactSurfaceBoundaryGluedAreaMeasure_seam_null :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
      (compactSurfaceBoundaryGluingSeam (identification := identification)) = 0 := by
  let seam := compactSurfaceBoundaryGluingSeam (identification := identification)
  have seamMeasurable : MeasurableSet seam :=
    (compactSurfaceBoundaryGluingSeam_isCompact
      (identification := identification)).isClosed.measurableSet
  have leftPreimage :
      (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ⁻¹' seam ⊆
        IL.boundary SL := by
    intro point membership
    rcases Set.mem_iUnion.mp membership with ⟨pair, pointMembership⟩
    rcases pointMembership with ⟨circlePoint, equality⟩
    have pointEquality : point = identification.leftBoundaryPoint pair circlePoint :=
      (CompactSurfaceBoundaryGluingQuotient.leftInclusion_injective identification)
        equality.symm
    subst point
    exact (leftPresentation.parameterization_mem_boundary_component
      (identification.leftComponent pair) circlePoint).choose
  have rightPreimage :
      (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) ⁻¹' seam ⊆
        IR.boundary SR := by
    intro point membership
    rcases Set.mem_iUnion.mp membership with ⟨pair, pointMembership⟩
    rcases pointMembership with ⟨circlePoint, equality⟩
    have crossing :=
      (CompactSurfaceBoundaryGluingQuotient.leftInclusion_eq_rightInclusion_iff
        (identification := identification)
        (identification.leftBoundaryPoint pair circlePoint) point).mp equality
    rcases crossing with ⟨otherPair, otherCirclePoint, _leftEquality, rightEquality⟩
    rw [rightEquality]
    exact (rightPresentation.parameterization_mem_boundary_component
      (identification.rightComponent otherPair)
      (identification.circleDiffeomorphism otherPair otherCirclePoint)).choose
  rw [compactSurfaceBoundaryGluedAreaMeasure, Measure.add_apply,
    Measure.map_apply_of_aemeasurable
      ((CompactSurfaceBoundaryGluingQuotient.sideInclusions_measurable identification).1.aemeasurable)
      seamMeasurable,
    Measure.map_apply_of_aemeasurable
      ((CompactSurfaceBoundaryGluingQuotient.sideInclusions_measurable identification).2.aemeasurable)
      seamMeasurable]
  rw [measure_mono_null leftPreimage leftSurface.boundary_null,
    measure_mono_null rightPreimage rightSurface.boundary_null, add_zero]

end

end YangMills.Geometry
