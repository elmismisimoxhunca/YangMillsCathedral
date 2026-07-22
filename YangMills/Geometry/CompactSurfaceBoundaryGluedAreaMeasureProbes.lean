/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryGluedAreaMeasure

/-!
# Hostile probes for the canonical glued area measure
-/

namespace YangMills.Geometry.CompactSurfaceBoundaryGluedAreaMeasure.Probes

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

/-- The exact candidate retains both pushforwards and its total area is their exact sum. -/
theorem exact_sum_pushforward_and_total :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification) =
        Measure.map (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
            leftSurface.areaMeasure +
          Measure.map (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
            rightSurface.areaMeasure ∧
      compactSurfaceBoundaryGluedAreaMeasure (identification := identification) Set.univ =
        leftSurface.areaMeasure Set.univ + rightSurface.areaMeasure Set.univ :=
  ⟨rfl, compactSurfaceBoundaryGluedAreaMeasure_univ⟩

/-- The canonical candidate is finite, positive, and nonzero. -/
theorem exact_finite_positive_nonzero :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification) Set.univ ≠ ⊤ ∧
      0 < compactSurfaceBoundaryGluedAreaMeasure (identification := identification) Set.univ ∧
      compactSurfaceBoundaryGluedAreaMeasure (identification := identification) ≠ 0 :=
  ⟨compactSurfaceBoundaryGluedAreaMeasure_ne_top,
    compactSurfaceBoundaryGluedAreaMeasure_pos,
    compactSurfaceBoundaryGluedAreaMeasure_ne_zero⟩

/-- Every measurable subset of either side retains exactly its original measure after embedding
into the glued quotient; this is stronger than total-area preservation alone. -/
theorem exact_measurable_side_restrictions
    {leftSubset : Set SL} (leftMeasurable : MeasurableSet leftSubset)
    {rightSubset : Set SR} (rightMeasurable : MeasurableSet rightSubset) :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
        (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification '' leftSubset) =
      leftSurface.areaMeasure leftSubset ∧
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
        (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification '' rightSubset) =
      rightSurface.areaMeasure rightSubset :=
  ⟨compactSurfaceBoundaryGluedAreaMeasure_left_image_apply leftMeasurable,
    compactSurfaceBoundaryGluedAreaMeasure_right_image_apply rightMeasurable⟩

/-- Each whole-side image retains exactly its original total area; the opposite side contributes
only through a null boundary preimage. -/
theorem exact_whole_side_image_areas :
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
        (Set.range (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)) =
      leftSurface.areaMeasure Set.univ ∧
    compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
        (Set.range (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)) =
      rightSurface.areaMeasure Set.univ :=
  ⟨compactSurfaceBoundaryGluedAreaMeasure_leftImage,
    compactSurfaceBoundaryGluedAreaMeasure_rightImage⟩

/-- The exact glued seam is compact, measurable, and null under the canonical area candidate. -/
theorem exact_compact_null_seam :
    IsCompact (compactSurfaceBoundaryGluingSeam (identification := identification)) ∧
      MeasurableSet (compactSurfaceBoundaryGluingSeam (identification := identification)) ∧
      compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
        (compactSurfaceBoundaryGluingSeam (identification := identification)) = 0 :=
  ⟨compactSurfaceBoundaryGluingSeam_isCompact,
    compactSurfaceBoundaryGluingSeam_isCompact.isClosed.measurableSet,
    compactSurfaceBoundaryGluedAreaMeasure_seam_null⟩

/-- A claimed positive seam area contradicts the exact side-boundary preimage calculation. -/
theorem positive_seam_area_blocked
    (wrongPositive : 0 < compactSurfaceBoundaryGluedAreaMeasure
      (identification := identification)
      (compactSurfaceBoundaryGluingSeam (identification := identification))) : False := by
  rw [compactSurfaceBoundaryGluedAreaMeasure_seam_null] at wrongPositive
  exact (lt_irrefl 0 wrongPositive)

/-- A zero candidate is hostilely rejected by the derived positive total area. -/
theorem zero_glued_measure_blocked
    (claimed : compactSurfaceBoundaryGluedAreaMeasure (identification := identification) = 0) :
    False :=
  compactSurfaceBoundaryGluedAreaMeasure_ne_zero claimed

end

end YangMills.Geometry.CompactSurfaceBoundaryGluedAreaMeasure.Probes
