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

/-- Compactness is derived from the compact disjoint union and quotient projection, rather than
supplied by later smooth-descent acceptance data. -/
@[reducible] def exact_quotient_compactSpace :
    CompactSpace (CompactSurfaceBoundaryGluingQuotient identification) :=
  inferInstance

/-- Positive-arity gluing joins the two connected side images, deriving connectedness rather than
leaving it to the later smooth-descent record. -/
@[reducible] def exact_quotient_connectedSpace :
    ConnectedSpace (CompactSurfaceBoundaryGluingQuotient identification) :=
  inferInstance

/-- The generated relation is exactly equality or one designated matching edge in either direction;
no longer chains create additional identifications. -/
theorem exact_generated_relation (first second : SL ⊕ SR) :
    Relation.EqvGen (compactSurfaceBoundaryGluingRelation identification) first second ↔
      first = second ∨
        compactSurfaceBoundaryGluingRelation identification first second ∨
        compactSurfaceBoundaryGluingRelation identification second first :=
  CompactSurfaceBoundaryGluingQuotient.eqvGen_iff_explicitGluingEquivalence
    identification first second

/-- Neither full side is collapsed by the quotient. -/
theorem exact_side_injectivity :
    Function.Injective (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Function.Injective (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) :=
  ⟨CompactSurfaceBoundaryGluingQuotient.leftInclusion_injective identification,
    CompactSurfaceBoundaryGluingQuotient.rightInclusion_injective identification⟩

/-- The two full-side ranges cover the exact quotient. -/
theorem exact_side_range_cover :
    Set.range (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∪
      Set.range (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) = Set.univ :=
  CompactSurfaceBoundaryGluingQuotient.range_leftInclusion_union_range_rightInclusion identification

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
