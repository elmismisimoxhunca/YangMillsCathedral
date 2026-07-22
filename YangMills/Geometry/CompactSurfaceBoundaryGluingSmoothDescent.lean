/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient
import YangMills.Geometry.CompactOrientedMeasuredSurfaceBoundaryNull
import YangMills.Geometry.CompactSurfaceBoundaryGluedAreaMeasure

/-!
# Smooth, oriented, measured descent obligations for compact-surface gluing

The exact topological quotient carrier was constructed separately. This file packages the irreducible
source-facing obligation that the same quotient topology carries the expected compact oriented
measured surface structure after gluing. It does not construct that structure.

The record requires genuine smooth embeddings of both full sides, exact pullback coherence of the
selected orientation forms, the sum pushforward area measure, disappearance of precisely the glued
boundary components, and interior placement of every seam point. Unselected boundary components are
retained exactly. No probability or Yang--Mills law is included.
-/

namespace YangMills.Geometry

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uEG uHG

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
    {identification : CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}

/-- Exact union of the selected left boundary components. -/
def selectedLeftBoundarySet : Set SL :=
  ⋃ pair : Fin identification.pairCount,
    compactSurfaceBoundaryComponentSet leftSurface (identification.leftComponent pair)

/-- Exact union of the selected right boundary components. -/
def selectedRightBoundarySet : Set SR :=
  ⋃ pair : Fin identification.pairCount,
    compactSurfaceBoundaryComponentSet rightSurface (identification.rightComponent pair)

abbrev GluedSurfaceCarrier := CompactSurfaceBoundaryGluingQuotient identification

variable
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [MeasurableSpace EG] [BorelSpace EG]
    {HG : Type uHG} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG (GluedSurfaceCarrier (identification := identification))]
    [IsManifold IG ∞ (GluedSurfaceCarrier (identification := identification))]

/-- Uninhabited exact descent contract on the already constructed topological quotient carrier. -/
structure CompactSurfaceBoundaryGluingSmoothDescentData where
  /-- The quotient with the supplied atlas and measure is itself an exact compact oriented measured
  surface nucleus. -/
  gluedSurface : CompactOrientedMeasuredSurfaceData IG
    (GluedSurfaceCarrier (identification := identification))
  /-- The only remaining differential obligation for each full-side map is immersion. Their exact
  topological embedding property has already been derived from the quotient construction. -/
  left_immersion : Manifold.IsImmersion IL IG ∞
    (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
  right_immersion : Manifold.IsImmersion IR IG ∞
    (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
  /-- Pullback of the glued orientation representative lies in exactly the same orientation class
  as each selected side form. Positive pointwise scales are retained because Lévy specifies
  orientations, not equality of arbitrarily normalized top-form representatives. -/
  left_orientationScale : SL → ℝ
  left_orientationScale_pos : ∀ point, 0 < left_orientationScale point
  right_orientationScale : SR → ℝ
  right_orientationScale_pos : ∀ point, 0 < right_orientationScale point
  left_orientation_pullback : ∀ point
      (vectors : Fin 2 → TangentSpace IL point),
    gluedSurface.orientationForm.toForm
        (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification point)
        (fun index => mfderiv IL IG
          (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) point
          (vectors index)) =
      left_orientationScale point * leftSurface.orientationForm.toForm point vectors
  right_orientation_pullback : ∀ point
      (vectors : Fin 2 → TangentSpace IR point),
    gluedSurface.orientationForm.toForm
        (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification point)
        (fun index => mfderiv IR IG
          (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) point
          (vectors index)) =
      right_orientationScale point * rightSurface.orientationForm.toForm point vectors
  /-- The glued area is exactly the sum of the two pushforwards. Nullity of both full side
  boundaries is derived from each surface's chart-density law and compactness, rather than stored
  as descent data. -/
  areaMeasure_eq_gluedAreaMeasure :
    gluedSurface.areaMeasure =
      compactSurfaceBoundaryGluedAreaMeasure (identification := identification)
  /-- Exactly the unselected side boundaries remain boundary after gluing. -/
  boundary_eq_unselected_images :
    IG.boundary (GluedSurfaceCarrier (identification := identification)) =
      CompactSurfaceBoundaryGluingQuotient.leftInclusion identification ''
          (IL.boundary SL \ selectedLeftBoundarySet (identification := identification)) ∪
        CompactSurfaceBoundaryGluingQuotient.rightInclusion identification ''
          (IR.boundary SR \ selectedRightBoundarySet (identification := identification))
namespace CompactSurfaceBoundaryGluingSmoothDescentData

/-- The left side map is a genuine smooth embedding: only immersion comes from descent data, while
the exact topological embedding is derived from the quotient. -/
theorem left_smoothEmbedding
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Manifold.IsSmoothEmbedding IL IG ∞
      (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) :=
  ⟨descent.left_immersion,
    (CompactSurfaceBoundaryGluingQuotient.leftInclusion_isClosedEmbedding
      identification).isEmbedding⟩

/-- The right side map is a genuine smooth embedding by the same differential/topological split. -/
theorem right_smoothEmbedding
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Manifold.IsSmoothEmbedding IR IG ∞
      (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) :=
  ⟨descent.right_immersion,
    (CompactSurfaceBoundaryGluingQuotient.rightInclusion_isClosedEmbedding
      identification).isEmbedding⟩

omit [FiniteDimensional ℝ EG] [MeasurableSpace EG] [BorelSpace EG]
  [IsManifold IG ∞ (GluedSurfaceCarrier (identification := identification))] in
/-- If the glued manifold boundary is exactly the unselected side-boundary images, then every
selected seam point is interior. Exact same-side injectivity and cross-side matching exclude both
parts of the displayed boundary. -/
theorem seam_mem_interior_of_boundary_eq
    (boundaryEq :
      IG.boundary (GluedSurfaceCarrier (identification := identification)) =
        CompactSurfaceBoundaryGluingQuotient.leftInclusion identification ''
            (IL.boundary SL \ selectedLeftBoundarySet (identification := identification)) ∪
          CompactSurfaceBoundaryGluingQuotient.rightInclusion identification ''
            (IR.boundary SR \ selectedRightBoundarySet (identification := identification)))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint) ∈
      IG.interior (GluedSurfaceCarrier (identification := identification)) := by
  rw [← IG.compl_boundary]
  intro boundaryMembership
  rw [boundaryEq] at boundaryMembership
  rcases boundaryMembership with leftImage | rightImage
  · rcases leftImage with ⟨leftPoint, ⟨_leftBoundary, leftUnselected⟩, equality⟩
    have pointEquality : leftPoint = identification.leftBoundaryPoint pair circlePoint :=
      (CompactSurfaceBoundaryGluingQuotient.leftInclusion_injective identification) equality
    apply leftUnselected
    subst leftPoint
    apply Set.mem_iUnion.mpr
    refine ⟨pair, ?_⟩
    rw [← leftPresentation.parameterization_range]
    exact ⟨circlePoint, rfl⟩
  · rcases rightImage with ⟨rightPoint, ⟨_rightBoundary, rightUnselected⟩, equality⟩
    have crossing :=
      (CompactSurfaceBoundaryGluingQuotient.leftInclusion_eq_rightInclusion_iff
        (identification := identification)
        (identification.leftBoundaryPoint pair circlePoint) rightPoint).mp equality.symm
    rcases crossing with ⟨otherPair, otherCirclePoint, _leftEquality, rightEquality⟩
    apply rightUnselected
    apply Set.mem_iUnion.mpr
    refine ⟨otherPair, ?_⟩
    rw [← rightPresentation.parameterization_range]
    exact ⟨identification.circleDiffeomorphism otherPair otherCirclePoint,
      rightEquality.symm⟩

/-- Every selected seam point is interior, derived from the exact remaining-boundary equation rather
than supplied as an independent descent field. -/
theorem seam_mem_interior
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint) ∈
      IG.interior (GluedSurfaceCarrier (identification := identification)) :=
  seam_mem_interior_of_boundary_eq descent.boundary_eq_unselected_images pair circlePoint

/-- Exact dimension two is inherited from the glued compact-surface nucleus. -/
theorem glued_model_finrank_two
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Module.finrank ℝ EG = 2 :=
  descent.gluedSurface.model_finrank_two

/-- The descended surface measure is the explicit sum of the two side pushforwards. -/
theorem areaMeasure_eq_sum_pushforward
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    descent.gluedSurface.areaMeasure =
      Measure.map (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification)
          leftSurface.areaMeasure +
        Measure.map (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification)
          rightSurface.areaMeasure := by
  simpa [compactSurfaceBoundaryGluedAreaMeasure] using descent.areaMeasure_eq_gluedAreaMeasure

/-- Both full side boundaries are null under their designated surface measures. This is inherited
from the surface chart-density theorem and is independent of any gluing descent witness. -/
theorem side_boundaries_null
    (_descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    leftSurface.areaMeasure (IL.boundary SL) = 0 ∧
      rightSurface.areaMeasure (IR.boundary SR) = 0 :=
  ⟨leftSurface.boundary_null, rightSurface.boundary_null⟩

/-- Both side inclusions are measurable, so the area pushforwards cannot use `Measure.map`'s
nonmeasurable zero fallback. -/
theorem sideInclusions_measurable
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG)) :
    Measurable (CompactSurfaceBoundaryGluingQuotient.leftInclusion identification) ∧
      Measurable (CompactSurfaceBoundaryGluingQuotient.rightInclusion identification) :=
  ⟨descent.left_smoothEmbedding.contMDiff.continuous.measurable,
    descent.right_smoothEmbedding.contMDiff.continuous.measurable⟩

/-- The two canonical side maps agree on every exact paired seam point in the same smooth carrier. -/
theorem paired_points_equal
    (_descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint) =
      CompactSurfaceBoundaryGluingQuotient.rightInclusion identification
        (identification.rightBoundaryPoint pair circlePoint) :=
  CompactSurfaceBoundaryGluingQuotient.paired_boundary_points_equal
    identification pair circlePoint

/-- Every seam point is not in the remaining manifold boundary. -/
theorem seam_not_mem_boundary
    (descent : CompactSurfaceBoundaryGluingSmoothDescentData
      (identification := identification) (IG := IG))
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint) ∉
      IG.boundary (GluedSurfaceCarrier (identification := identification)) := by
  intro boundaryMembership
  exact Set.disjoint_left.mp IG.disjoint_interior_boundary
    (descent.seam_mem_interior pair circlePoint) boundaryMembership

end CompactSurfaceBoundaryGluingSmoothDescentData

end

end YangMills.Geometry
