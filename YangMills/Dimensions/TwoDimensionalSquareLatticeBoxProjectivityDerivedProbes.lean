/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectivityDerived

/-!
# Hostile probes for derived square-box projectivity
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectivityDerived.Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G)

/-- Every normalized Definition 7.1 action now constructs the exact projectivity datum. -/
@[reducible] def exact_constructed_projectivity :
    TwoDimensionalSquareLatticeBoxProjectiveConsistencyData spacing action :=
  twoDimensionalSquareLatticeBoxProjectiveConsistencyData spacing action

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The plaquette marginal and the coordinate/plaquette commuting square retain the literal
successor inclusions. -/
theorem exact_restriction_square
    (radius : PositiveSquareLatticeBoxRadius)
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing
      (squareLatticeBoxSuccessorRadius radius) → G) :
    Measurable (epsilonSquareLatticeBoxPlaquetteValueRestriction (G := G) spacing radius) ∧
      boxPlaquetteDifferenceForward spacing radius
          (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration) =
        epsilonSquareLatticeBoxPlaquetteValueRestriction spacing radius
          (boxPlaquetteDifferenceForward spacing
            (squareLatticeBoxSuccessorRadius radius) configuration) :=
  ⟨epsilonSquareLatticeBoxPlaquetteValueRestriction.measurable spacing radius,
    boxPlaquetteDifferenceForward_restriction_commutes spacing radius configuration⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Independent plaquette action products have the exact literal smaller marginal. -/
theorem exact_plaquette_product_marginal (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (epsilonSquareLatticeBoxPlaquetteValueRestriction (G := G) spacing radius)
      (twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing
          (squareLatticeBoxSuccessorRadius radius)) action) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action :=
  map_plaquetteActionFiniteProduct_restriction spacing radius action

/-- The constructed coordinate laws satisfy the exact consecutive pushforward directly. -/
theorem exact_consecutive_box_pushforward (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius)
        (twoDimensionalSquareLatticeBoxMeasure spacing
          (squareLatticeBoxSuccessorRadius radius) action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action :=
  twoDimensionalSquareLatticeBoxMeasure_consecutive_pushforward spacing radius action

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- A changed plaquette restriction square is rejected when it differs from the exact literal
restriction. -/
theorem changed_restriction_square_blocked
    (radius : PositiveSquareLatticeBoxRadius)
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing
      (squareLatticeBoxSuccessorRadius radius) → G)
    (wrong : EpsilonSquareLatticeBoxPlaquette spacing radius → G)
    (different : wrong ≠ epsilonSquareLatticeBoxPlaquetteValueRestriction spacing radius
      (boxPlaquetteDifferenceForward spacing
        (squareLatticeBoxSuccessorRadius radius) configuration))
    (claimed : wrong = boxPlaquetteDifferenceForward spacing radius
      (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration)) : False := by
  apply different
  rw [claimed]
  exact boxPlaquetteDifferenceForward_restriction_commutes
    spacing radius configuration

/-- A claimed failure of the exact successor pushforward contradicts the derived theorem, without
requiring a separately supplied consistency witness. -/
theorem inconsistent_successor_blocked
    (radius : PositiveSquareLatticeBoxRadius)
    (failure : Measure.map
      (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius)
      (twoDimensionalSquareLatticeBoxMeasure spacing
        (squareLatticeBoxSuccessorRadius radius) action) ≠
      twoDimensionalSquareLatticeBoxMeasure spacing radius action) : False :=
  failure (twoDimensionalSquareLatticeBoxMeasure_consecutive_pushforward
    spacing radius action)

/-- Derived two-dimensional finite-box projectivity remains distinct from the four-dimensional
continuum endpoint. -/
theorem derived_projectivity_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectivityDerived.Probes
