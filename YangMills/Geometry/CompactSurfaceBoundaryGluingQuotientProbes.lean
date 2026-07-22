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

/-- Closed-equivalence separation derives Hausdorffness rather than leaving it as a smooth-descent
assumption. -/
@[reducible] def exact_quotient_t2Space :
    T2Space (CompactSurfaceBoundaryGluingQuotient identification) :=
  inferInstance

/-- Compact-fiber saturated cores derive second countability rather than leaving it as a
smooth-descent assumption. -/
@[reducible] def exact_quotient_secondCountableTopology :
    SecondCountableTopology (CompactSurfaceBoundaryGluingQuotient identification) :=
  inferInstance

/-- The explicit countable saturated-core family is a genuine topological basis. -/
theorem exact_quotient_core_basis :
    TopologicalSpace.IsTopologicalBasis
      (CompactSurfaceBoundaryGluingQuotient.quotientCoreBasis identification) :=
  CompactSurfaceBoundaryGluingQuotient.quotientCoreBasis_isTopologicalBasis identification

/-- Distinct quotient points have explicit disjoint open neighborhoods. -/
theorem exact_disjoint_open_neighborhoods
    {first second : CompactSurfaceBoundaryGluingQuotient identification}
    (distinct : first ≠ second) :
    ∃ firstOpen secondOpen : Set (CompactSurfaceBoundaryGluingQuotient identification),
      IsOpen firstOpen ∧ IsOpen secondOpen ∧ first ∈ firstOpen ∧ second ∈ secondOpen ∧
        Disjoint firstOpen secondOpen :=
  CompactSurfaceBoundaryGluingQuotient.exists_disjoint_open_neighborhoods
    identification first second distinct

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

/-- The primitive relation is a finite union of compact circle graphs, and the exact generated
equivalence relation is closed in the Hausdorff disjoint-union square. -/
theorem exact_closed_generated_relation :
    IsClosed {points : (SL ⊕ SR) × (SL ⊕ SR) |
      CompactSurfaceBoundaryGluingQuotient.explicitGluingEquivalence
        identification points.1 points.2} :=
  CompactSurfaceBoundaryGluingQuotient.explicitGluingEquivalence_set_isClosed identification

/-- Each actual seam graph is continuous with closed range. -/
theorem exact_seam_graph_closed (pair : Fin identification.pairCount) :
    Continuous (CompactSurfaceBoundaryGluingQuotient.boundarySeamGraph identification pair) ∧
      IsClosed (Set.range
        (CompactSurfaceBoundaryGluingQuotient.boundarySeamGraph identification pair)) :=
  ⟨CompactSurfaceBoundaryGluingQuotient.boundarySeamGraph_continuous identification pair,
    CompactSurfaceBoundaryGluingQuotient.boundarySeamGraph_range_isClosed identification pair⟩

/-- Closed subsets have closed exact saturations, making the quotient projection a closed map
without assuming that its product map is quotient. -/
theorem exact_closed_saturation_and_projection
    (subset : Set (SL ⊕ SR)) (subsetClosed : IsClosed subset) :
    IsClosed (CompactSurfaceBoundaryGluingQuotient.explicitGluingSaturation
      identification subset) ∧
      IsClosedMap (CompactSurfaceBoundaryGluingQuotient.projection identification) :=
  ⟨CompactSurfaceBoundaryGluingQuotient.explicitGluingSaturation_isClosed
      identification subsetClosed,
    CompactSurfaceBoundaryGluingQuotient.projection_isClosedMap identification⟩

/-- Neither full side is collapsed by the quotient. -/
theorem exact_side_injectivity :
    Function.Injective (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Function.Injective (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) ∧
      Topology.IsClosedEmbedding
        (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Topology.IsClosedEmbedding
        (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) :=
  ⟨CompactSurfaceBoundaryGluingQuotient.leftInclusion_injective identification,
    CompactSurfaceBoundaryGluingQuotient.rightInclusion_injective identification,
    CompactSurfaceBoundaryGluingQuotient.leftInclusion_isClosedEmbedding identification,
    CompactSurfaceBoundaryGluingQuotient.rightInclusion_isClosedEmbedding identification⟩

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
