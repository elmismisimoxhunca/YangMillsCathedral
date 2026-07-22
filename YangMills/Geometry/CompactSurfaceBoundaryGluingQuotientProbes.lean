/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient

/-!
# Hostile probes for the exact compact-surface boundary-gluing quotient
-/

namespace YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.Probes

open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uTarget

variable
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL]
    {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER]
    {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : CompactSurfaceBoundaryOrientationData leftSurface leftPresentation}
    {rightSurface : CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : CompactSurfaceBoundaryOrientationData rightSurface rightPresentation}
    (identification : CompactSurfaceBoundaryIdentification leftSurface leftPresentation
      leftOrientation rightSurface rightPresentation rightOrientation)

/-- The carrier is definitionally the quotient by the equivalence closure of the exact primitive
boundary-pair relation, not an unrelated quotient. -/
theorem exact_equivalence_closure_carrier :
    CompactSurfaceBoundaryGluingQuotient identification =
      Quot (Relation.EqvGen (compactSurfaceBoundaryGluingRelation identification)) :=
  rfl

/-- Primitive generators cannot identify two left points directly. Any same-side equality must come
from the minimal equivalence closure, not from an extra primitive relation. -/
theorem no_primitive_left_left_relation (first second : SL) :
    ¬ compactSurfaceBoundaryGluingRelation identification
      (Sum.inl first) (Sum.inl second) := by
  simp [compactSurfaceBoundaryGluingRelation]

/-- Primitive generators cannot identify two right points directly. -/
theorem no_primitive_right_right_relation (first second : SR) :
    ¬ compactSurfaceBoundaryGluingRelation identification
      (Sum.inr first) (Sum.inr second) := by
  simp [compactSurfaceBoundaryGluingRelation]

/-- Every designated paired boundary point is literally equal in the exact quotient. -/
theorem exact_paired_points_equal (pair : Fin identification.pairCount)
    (circlePoint : Circle) :
    CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint) =
      CompactSurfaceBoundaryGluingQuotient.rightInclusion identification
        (identification.rightBoundaryPoint pair circlePoint) :=
  CompactSurfaceBoundaryGluingQuotient.paired_boundary_points_equal identification pair circlePoint

/-- The projection carries the genuine quotient topology and quotient-map universal topology. -/
theorem exact_topological_quotient_projection :
    Continuous (CompactSurfaceBoundaryGluingQuotient.projection identification) ∧
      Topology.IsQuotientMap (CompactSurfaceBoundaryGluingQuotient.projection identification) :=
  ⟨CompactSurfaceBoundaryGluingQuotient.projection_continuous identification,
    CompactSurfaceBoundaryGluingQuotient.projection_isQuotientMap identification⟩

/-- Sidewise functions descend only when they agree on every exact paired point, and the descended
function recovers both originals. -/
theorem exact_universal_lift {Target : Type uTarget}
    (leftFunction : SL → Target) (rightFunction : SR → Target)
    (compatible : ∀ (pair : Fin identification.pairCount) (circlePoint : Circle),
      leftFunction (identification.leftBoundaryPoint pair circlePoint) =
        rightFunction (identification.rightBoundaryPoint pair circlePoint)) :
    (∀ point : SL,
      CompactSurfaceBoundaryGluingQuotient.lift identification
        leftFunction rightFunction compatible
        (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification point) =
          leftFunction point) ∧
    (∀ point : SR,
      CompactSurfaceBoundaryGluingQuotient.lift identification
        leftFunction rightFunction compatible
        (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification point) =
          rightFunction point) :=
  ⟨CompactSurfaceBoundaryGluingQuotient.lift_left identification
      leftFunction rightFunction compatible,
    CompactSurfaceBoundaryGluingQuotient.lift_right identification
      leftFunction rightFunction compatible⟩

end

end YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.Probes
