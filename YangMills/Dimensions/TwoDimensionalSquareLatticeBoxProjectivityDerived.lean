/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxActionFactorization
import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveConsistency
import YangMills.Mathematics.FiniteProductRestriction

/-!
# Derived consecutive projectivity of exact square-box laws

Literal coordinate and plaquette restrictions form a commuting square with the exact noncommutative
box holonomy equivalences. Independent plaquette-action products have the required marginal by the
general finite-product restriction theorem. Conjugating that marginal through the commuting square
derives exact consecutive projective consistency for every normalized Driver Definition 7.1 action.

This proves only finite-box projectivity. It constructs no infinite-volume or continuum limit.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG

/-- Restr successor-box plaquette values to the literally included smaller plaquettes. -/
def epsilonSquareLatticeBoxPlaquetteValueRestriction
    {G : Type uG}
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    (EpsilonSquareLatticeBoxPlaquette spacing (squareLatticeBoxSuccessorRadius radius) → G) →
      (EpsilonSquareLatticeBoxPlaquette spacing radius → G) :=
  finiteProductRestriction (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius)

namespace epsilonSquareLatticeBoxPlaquetteValueRestriction

/-- Plaquette-value restriction is measurable for every measurable target. -/
theorem measurable
    {G : Type uG} [MeasurableSpace G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Measurable (epsilonSquareLatticeBoxPlaquetteValueRestriction (G := G) spacing radius) := by
  apply measurable_pi_iff.mpr
  intro plaquette
  exact measurable_pi_apply (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius plaquette)

end epsilonSquareLatticeBoxPlaquetteValueRestriction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Small- and successor-box axial extensions agree on every boundary bond of every included small
plaquette after literal coordinate restriction. -/
theorem epsilonSquareLatticeBoxAxialExtension_restriction_on_plaquetteBoundary
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing
      (squareLatticeBoxSuccessorRadius radius) → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (boundaryMembership : bond ∈ plaquette.1.boundaryBonds) :
    epsilonSquareLatticeBoxAxialExtension spacing radius
        (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration) bond =
      epsilonSquareLatticeBoxAxialExtension spacing
        (squareLatticeBoxSuccessorRadius radius) configuration bond := by
  rcases epsilonSquareLatticeBoxAxialCoordinates.plaquette_boundary_covered
    spacing radius plaquette.1 plaquette.2 bond boundaryMembership with
      tree | forward | reverse
  · rw [(epsilonSquareLatticeBoxAxialExtension spacing radius
      (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration)).axialTree_fixed
        bond tree]
    rw [(epsilonSquareLatticeBoxAxialExtension spacing
      (squareLatticeBoxSuccessorRadius radius) configuration).axialTree_fixed bond tree]
  · let smallCoordinate : EpsilonSquareLatticeBoxCoordinate spacing radius := ⟨bond, forward⟩
    let largeCoordinate := epsilonSquareLatticeBoxCoordinateInclusion spacing radius smallCoordinate
    rw [show epsilonSquareLatticeBoxAxialExtension spacing radius
      (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration) bond =
        epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration smallCoordinate by
      exact epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius _ smallCoordinate]
    rw [show epsilonSquareLatticeBoxAxialExtension spacing
      (squareLatticeBoxSuccessorRadius radius) configuration bond = configuration largeCoordinate by
      simpa [largeCoordinate, smallCoordinate] using
        epsilonSquareLatticeBoxAxialExtension.coordinate spacing
          (squareLatticeBoxSuccessorRadius radius) configuration largeCoordinate]
    rfl
  · let smallCoordinate : EpsilonSquareLatticeBoxCoordinate spacing radius := ⟨bond.reverse, reverse⟩
    let largeCoordinate := epsilonSquareLatticeBoxCoordinateInclusion spacing radius smallCoordinate
    have smallReverse :
        epsilonSquareLatticeBoxAxialExtension spacing radius
            (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration) bond =
          (epsilonSquareLatticeBoxAxialExtension spacing radius
            (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration)
              bond.reverse)⁻¹ := by
      simpa using (epsilonSquareLatticeBoxAxialExtension spacing radius
        (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration)).configuration.reverse_value
          bond.reverse
    have largeReverse :
        epsilonSquareLatticeBoxAxialExtension spacing
            (squareLatticeBoxSuccessorRadius radius) configuration bond =
          (epsilonSquareLatticeBoxAxialExtension spacing
            (squareLatticeBoxSuccessorRadius radius) configuration bond.reverse)⁻¹ := by
      simpa using (epsilonSquareLatticeBoxAxialExtension spacing
        (squareLatticeBoxSuccessorRadius radius) configuration).configuration.reverse_value
          bond.reverse
    rw [smallReverse, largeReverse]
    congr 1
    rw [show epsilonSquareLatticeBoxAxialExtension spacing radius
      (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration) bond.reverse =
        epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration smallCoordinate by
      exact epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius _ smallCoordinate]
    rw [show epsilonSquareLatticeBoxAxialExtension spacing
      (squareLatticeBoxSuccessorRadius radius) configuration bond.reverse = configuration largeCoordinate by
      simpa [largeCoordinate, smallCoordinate] using
        epsilonSquareLatticeBoxAxialExtension.coordinate spacing
          (squareLatticeBoxSuccessorRadius radius) configuration largeCoordinate]
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Consequently the same included small plaquette has identical noncommutative holonomy in the
small restricted extension and successor extension. -/
theorem epsilonSquareLatticeBoxAxialPlaquetteHolonomy_restriction
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing
      (squareLatticeBoxSuccessorRadius radius) → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
      (epsilonSquareLatticeBoxAxialExtension spacing radius
        (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration)) =
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
      (epsilonSquareLatticeBoxAxialExtension spacing
        (squareLatticeBoxSuccessorRadius radius) configuration) := by
  unfold epsilonSquareLatticeAxialPlaquetteHolonomy epsilonSquareLatticePlaquetteHolonomy
  rw [epsilonSquareLatticeBoxAxialExtension_restriction_on_plaquetteBoundary
      spacing radius configuration plaquette plaquette.1.leftBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]
  rw [epsilonSquareLatticeBoxAxialExtension_restriction_on_plaquetteBoundary
      spacing radius configuration plaquette plaquette.1.topBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]
  rw [epsilonSquareLatticeBoxAxialExtension_restriction_on_plaquetteBoundary
      spacing radius configuration plaquette plaquette.1.rightBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]
  rw [epsilonSquareLatticeBoxAxialExtension_restriction_on_plaquetteBoundary
      spacing radius configuration plaquette plaquette.1.bottomBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The exact coordinate-to-plaquette difference transforms commute with literal consecutive box
restriction. -/
theorem boxPlaquetteDifferenceForward_restriction_commutes
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing
      (squareLatticeBoxSuccessorRadius radius) → G) :
    boxPlaquetteDifferenceForward spacing radius
        (epsilonSquareLatticeBoxCoordinateRestriction spacing radius configuration) =
      epsilonSquareLatticeBoxPlaquetteValueRestriction spacing radius
        (boxPlaquetteDifferenceForward spacing
          (squareLatticeBoxSuccessorRadius radius) configuration) := by
  funext plaquette
  rw [boxPlaquetteDifferenceForward_eq_holonomy]
  change _ = boxPlaquetteDifferenceForward spacing
    (squareLatticeBoxSuccessorRadius radius) configuration
      (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius plaquette)
  rw [boxPlaquetteDifferenceForward_eq_holonomy]
  change _ = epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
    (epsilonSquareLatticeBoxAxialExtension spacing
      (squareLatticeBoxSuccessorRadius radius) configuration)
  exact epsilonSquareLatticeBoxAxialPlaquetteHolonomy_restriction
    spacing radius configuration plaquette

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The independent successor plaquette-action product has the exact smaller product as its
literal plaquette marginal. -/
theorem map_plaquetteActionFiniteProduct_restriction
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (action : TwoDimensionalLatticeActionData G) :
    Measure.map (epsilonSquareLatticeBoxPlaquetteValueRestriction (G := G) spacing radius)
      (twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing (squareLatticeBoxSuccessorRadius radius)) action) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action := by
  let μ := twoDimensionalPlaquetteActionMeasure action
  letI : IsProbabilityMeasure μ :=
    twoDimensionalPlaquetteActionMeasure.instIsProbabilityMeasure action
  simpa [epsilonSquareLatticeBoxPlaquetteValueRestriction,
    twoDimensionalPlaquetteActionFiniteProduct, μ] using
    finiteProductRestriction.map_eq μ
      (epsilonSquareLatticeBoxPlaquetteInclusion spacing radius)
      (epsilonSquareLatticeBoxPlaquetteInclusion.injective spacing radius)

/-- Exact consecutive projective consistency of the constructed square-box laws. -/
theorem twoDimensionalSquareLatticeBoxMeasure_consecutive_pushforward
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (action : TwoDimensionalLatticeActionData G) :
    Measure.map (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius)
        (twoDimensionalSquareLatticeBoxMeasure spacing
          (squareLatticeBoxSuccessorRadius radius) action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action := by
  let coordinateRestriction :=
    epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing radius
  let plaquetteRestriction :=
    epsilonSquareLatticeBoxPlaquetteValueRestriction (G := G) spacing radius
  let largeForward := boxPlaquetteDifferenceForward (G := G) spacing
    (squareLatticeBoxSuccessorRadius radius)
  let smallForward := boxPlaquetteDifferenceForward (G := G) spacing radius
  let largeMeasure := twoDimensionalSquareLatticeBoxMeasure spacing
    (squareLatticeBoxSuccessorRadius radius) action
  let smallMeasure := twoDimensionalSquareLatticeBoxMeasure spacing radius action
  let largeProduct := twoDimensionalPlaquetteActionFiniteProduct
    (EpsilonSquareLatticeBoxPlaquette spacing (squareLatticeBoxSuccessorRadius radius)) action
  let smallProduct := twoDimensionalPlaquetteActionFiniteProduct
    (EpsilonSquareLatticeBoxPlaquette spacing radius) action
  have coordinateRestrictionMeasurable : Measurable coordinateRestriction :=
    epsilonSquareLatticeBoxCoordinateRestriction.measurable spacing radius
  have plaquetteRestrictionMeasurable : Measurable plaquetteRestriction :=
    epsilonSquareLatticeBoxPlaquetteValueRestriction.measurable spacing radius
  have largeForwardMeasurable : Measurable largeForward :=
    boxPlaquetteDifferenceForward_measurable spacing
      (squareLatticeBoxSuccessorRadius radius)
  have smallForwardMeasurable : Measurable smallForward :=
    boxPlaquetteDifferenceForward_measurable spacing radius
  have commuting : smallForward ∘ coordinateRestriction =
      plaquetteRestriction ∘ largeForward := by
    funext configuration
    exact boxPlaquetteDifferenceForward_restriction_commutes spacing radius configuration
  have largeFactor : Measure.map largeForward largeMeasure = largeProduct :=
    map_twoDimensionalSquareLatticeBoxMeasure_eq_plaquetteActionFiniteProduct spacing
      (squareLatticeBoxSuccessorRadius radius) action
  have smallFactor : Measure.map smallForward smallMeasure = smallProduct :=
    map_twoDimensionalSquareLatticeBoxMeasure_eq_plaquetteActionFiniteProduct
      spacing radius action
  have productMarginal : Measure.map plaquetteRestriction largeProduct = smallProduct :=
    map_plaquetteActionFiniteProduct_restriction spacing radius action
  have afterSmallForward :
      Measure.map smallForward (Measure.map coordinateRestriction largeMeasure) =
        Measure.map smallForward smallMeasure := by
    calc
      Measure.map smallForward (Measure.map coordinateRestriction largeMeasure) =
          Measure.map (smallForward ∘ coordinateRestriction) largeMeasure :=
        Measure.map_map smallForwardMeasurable coordinateRestrictionMeasurable
      _ = Measure.map (plaquetteRestriction ∘ largeForward) largeMeasure := by
        rw [commuting]
      _ = Measure.map plaquetteRestriction (Measure.map largeForward largeMeasure) :=
        (Measure.map_map plaquetteRestrictionMeasurable largeForwardMeasurable).symm
      _ = Measure.map plaquetteRestriction largeProduct := by rw [largeFactor]
      _ = smallProduct := productMarginal
      _ = Measure.map smallForward smallMeasure := smallFactor.symm
  change Measure.map (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius)
      (Measure.map coordinateRestriction largeMeasure) =
    Measure.map (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius) smallMeasure
    at afterSmallForward
  have mappedBack := congrArg
    (Measure.map (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius).symm)
    afterSmallForward
  simpa only [(boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius).map_symm_map]
    using mappedBack

/-- Constructed exact consecutive-box projective consistency for every normalized Definition 7.1
action. -/
def twoDimensionalSquareLatticeBoxProjectiveConsistencyData
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G) :
    TwoDimensionalSquareLatticeBoxProjectiveConsistencyData spacing action where
  consecutive_pushforward := fun radius =>
    twoDimensionalSquareLatticeBoxMeasure_consecutive_pushforward spacing radius action


end

end YangMills.Dimensions
