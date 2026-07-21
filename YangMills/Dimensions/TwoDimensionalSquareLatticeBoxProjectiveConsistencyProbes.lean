/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveConsistency

/-!
# Probes for exact-box projective consistency
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveConsistency.Probes

open MeasureTheory

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G)

/-- Successor radius is literally `n+1`. -/
theorem exact_successor_radius (radius : PositiveSquareLatticeBoxRadius) :
    (squareLatticeBoxSuccessorRadius radius).1 = radius.1 + 1 :=
  rfl

/-- Coordinate inclusion is injective and preserves the exact directed bond. -/
theorem exact_coordinate_inclusion (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (epsilonSquareLatticeBoxCoordinateInclusion spacing radius) ∧
      (∀ coordinate,
        (epsilonSquareLatticeBoxCoordinateInclusion spacing radius coordinate).1 = coordinate.1) :=
  ⟨epsilonSquareLatticeBoxCoordinateInclusion.injective spacing radius,
    epsilonSquareLatticeBoxCoordinateInclusion.val spacing radius⟩

/-- Plaquette inclusion is injective and preserves the exact elementary plaquette. -/
theorem exact_plaquette_inclusion (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius) ∧
      (∀ plaquette,
        (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius plaquette).1 = plaquette.1) :=
  ⟨epsilonSquareLatticeBoxPlaquetteInclusion.injective spacing radius,
    epsilonSquareLatticeBoxPlaquetteInclusion.val spacing radius⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Coordinate restriction is measurable. -/
theorem exact_restriction_measurable (radius : PositiveSquareLatticeBoxRadius) :
    Measurable (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius) :=
  epsilonSquareLatticeBoxCoordinateRestriction.measurable spacing radius

/-- The source-facing datum requires exact pushforward from every successor box. -/
theorem exact_consecutive_pushforward
    (consistency : TwoDimensionalSquareLatticeBoxProjectiveConsistencyData spacing action)
    (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius)
        (twoDimensionalSquareLatticeBoxMeasure spacing
          (squareLatticeBoxSuccessorRadius radius) action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action :=
  consistency.consecutive_pushforward radius

/-- A proposed failure of one exact successor pushforward is hostilely rejected. -/
theorem inconsistent_successor_blocked
    (consistency : TwoDimensionalSquareLatticeBoxProjectiveConsistencyData spacing action)
    (radius : PositiveSquareLatticeBoxRadius)
    (claimed : Measure.map
      (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius)
      (twoDimensionalSquareLatticeBoxMeasure spacing
        (squareLatticeBoxSuccessorRadius radius) action) ≠
      twoDimensionalSquareLatticeBoxMeasure spacing radius action) : False :=
  claimed (consistency.consecutive_pushforward radius)

/-- The interface does not identify finite-box consistency with a four-dimensional endpoint. -/
theorem projective_boxes_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveConsistency.Probes
