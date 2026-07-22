/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalInfiniteAxialCylinderLawConstructed
import YangMills.Dimensions.TwoDimensionalDriverAxialWeakLimit

/-!
# Hostile probes for the constructed infinite axial cylinder law
-/

namespace YangMills.Dimensions.TwoDimensionalInfiniteAxialCylinderLawConstructed.Probes

open MeasureTheory Set

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The global iid plaquette law has every exact finite plaquette-action product marginal. -/
theorem exact_global_plaquette_marginal (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (infinitePlaquetteBoxRestriction (G := G) spacing radius)
        (infinitePlaquetteActionProductMeasure spacing action) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action :=
  infinitePlaquetteActionProductMeasure_box_marginal spacing action radius

/-- The recovered infinite axial measure has every existing finite box law as an exact coordinate
cylinder, not merely as a weak limit. -/
theorem exact_global_coordinate_marginal (radius : PositiveSquareLatticeBoxRadius) :
    Measure.map (infiniteAxialBoxCoordinateRestriction (G := G) spacing radius)
        (infiniteAxialRecoveredMeasure spacing action) =
      twoDimensionalSquareLatticeBoxMeasure spacing radius action :=
  infiniteAxialRecoveredMeasure_box_marginal spacing action radius

/-- The projective infinite-cylinder interface is now concretely inhabited for exact square boxes. -/
@[reducible] def exact_constructed_cylinder_law :
    TwoDimensionalAxialInfiniteVolumeCylinderLawData (spacing := spacing) action
      (twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action) :=
  twoDimensionalSquareLatticeInfiniteAxialCylinderLawData spacing action

/-- Normalization and nonzeroness derive through the existing cylinder-law interface. -/
theorem exact_probability_nondegenerate :
    infiniteAxialRecoveredMeasure spacing action Set.univ = 1 ∧
      infiniteAxialRecoveredMeasure spacing action ≠ 0 :=
  ⟨(twoDimensionalSquareLatticeInfiniteAxialCylinderLawData spacing action).probability_normalized,
    (twoDimensionalSquareLatticeInfiniteAxialCylinderLawData spacing action).probabilityMeasure_ne_zero⟩

/-- A proposed infinite axial measure whose exact box marginal is wrong cannot equal the recovered
measure. -/
theorem wrong_infinite_measure_marginal_blocked
    (radius : PositiveSquareLatticeBoxRadius)
    (wrong : Measure (EpsilonSquareLatticeAxialConfiguration G spacing))
    (mismatch : Measure.map
      (infiniteAxialBoxCoordinateRestriction (G := G) spacing radius) wrong ≠
      twoDimensionalSquareLatticeBoxMeasure spacing radius action) :
    wrong ≠ infiniteAxialRecoveredMeasure spacing action := by
  intro equality
  subst wrong
  exact mismatch (infiniteAxialRecoveredMeasure_box_marginal spacing action radius)

/-- Changing one finite cylinder law is incompatible with the constructed infinite measure. -/
theorem changed_finite_cylinder_blocked
    (radius : PositiveSquareLatticeBoxRadius)
    (wrong : Measure (EpsilonSquareLatticeBoxCoordinate spacing radius → G))
    (different : wrong ≠ twoDimensionalSquareLatticeBoxMeasure spacing radius action)
    (claimed : Measure.map (infiniteAxialBoxCoordinateRestriction (G := G) spacing radius)
      (infiniteAxialRecoveredMeasure spacing action) = wrong) : False := by
  apply different
  rw [← claimed]
  exact infiniteAxialRecoveredMeasure_box_marginal spacing action radius

variable [T2Space G] [SecondCountableTopology G] in
/-- The constructed cylinder record can coexist with absence of Driver's stronger
boundary-conditioned weak-limit record; the former therefore cannot serve as the latter. -/
theorem constructed_cylinder_does_not_force_weak_limit
    (failure : ¬ Nonempty (TwoDimensionalDriverAxialWeakLimitData (G := G) spacing action)) :
    Nonempty (TwoDimensionalAxialInfiniteVolumeCylinderLawData (spacing := spacing) action
      (twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action)) ∧
      ¬ Nonempty (TwoDimensionalDriverAxialWeakLimitData (G := G) spacing action) :=
  ⟨⟨twoDimensionalSquareLatticeInfiniteAxialCylinderLawData spacing action⟩, failure⟩

/-- The actual constructed 2D cylinder witness is retained together with the proof that its
Euclidean dimension is not the 4D endpoint. -/
theorem constructed_cylinder_dimension_separation :
    Nonempty (TwoDimensionalAxialInfiniteVolumeCylinderLawData (spacing := spacing) action
      (twoDimensionalSquareLatticeBoxProjectiveSequenceData spacing action)) ∧
      EuclideanDimension.two ≠ EuclideanDimension.four :=
  ⟨⟨twoDimensionalSquareLatticeInfiniteAxialCylinderLawData spacing action⟩,
    EuclideanDimension.two_ne_four⟩

end

end YangMills.Dimensions.TwoDimensionalInfiniteAxialCylinderLawConstructed.Probes
