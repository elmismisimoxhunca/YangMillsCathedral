/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalInfiniteSquareLatticeConfiguration
import YangMills.Foundation.DimensionsProbes

/-!
# Probes for Driver's infinite square-lattice configuration carriers
-/

namespace YangMills.Dimensions.TwoDimensionalInfiniteSquareLatticeConfiguration.Probes

noncomputable section

variable {spacing : PositiveLatticeSpacing}

/-- A concrete vertical nearest-neighbor bond. -/
def verticalBond : EpsilonSquareLatticeDirectedBond spacing where
  source := (0, 1)
  target := (0, 2)
  nearestNeighbor := by
    right
    constructor
    · left
      norm_num
    · rfl

/-- A concrete horizontal bond strictly above the x-axis. -/
def horizontalAboveAxisBond : EpsilonSquareLatticeDirectedBond spacing where
  source := (0, 1)
  target := (1, 1)
  nearestNeighbor := by
    left
    constructor
    · left
      norm_num
    · rfl

/-- A concrete horizontal bond on the x-axis. -/
def horizontalAxisBond : EpsilonSquareLatticeDirectedBond spacing where
  source := (0, 0)
  target := (1, 0)
  nearestNeighbor := by
    left
    constructor
    · left
      norm_num
    · rfl

/-- Integer sites are physically embedded at exact spacing-sensitive `εℤ²` coordinates. -/
theorem exact_scaled_site (site : ℤ × ℤ) :
    twoDimensionalFirstCoordinate (epsilonSquareLatticePoint spacing site) =
        spacing.1 * (site.1 : ℝ) ∧
      twoDimensionalSecondCoordinate (epsilonSquareLatticePoint spacing site) =
        spacing.1 * (site.2 : ℝ) :=
  ⟨EpsilonSquareLatticeDirectedBond.point_firstCoordinate site,
    EpsilonSquareLatticeDirectedBond.point_secondCoordinate site⟩

/-- The concrete horizontal bond has physical displacement exactly `ε`, not unit displacement. -/
theorem exact_horizontal_physical_step :
    twoDimensionalFirstCoordinate
        (epsilonSquareLatticePoint spacing
          (horizontalAboveAxisBond (spacing := spacing)).target) =
      twoDimensionalFirstCoordinate
        (epsilonSquareLatticePoint spacing
          (horizontalAboveAxisBond (spacing := spacing)).source) + spacing.1 := by
  norm_num [horizontalAboveAxisBond]

/-- Every vertical bond is in Driver's axial tree. -/
theorem vertical_is_axial :
    epsilonSquareLatticeIsAxialTreeBond (verticalBond (spacing := spacing)) :=
  Or.inl rfl

/-- Horizontal x-axis bonds are in Driver's axial tree. -/
theorem horizontal_axis_is_axial :
    epsilonSquareLatticeIsAxialTreeBond (horizontalAxisBond (spacing := spacing)) :=
  Or.inr ⟨rfl, rfl⟩

/-- Horizontal bonds away from the x-axis remain unfrozen coordinates. -/
theorem horizontal_above_axis_not_axial :
    ¬ epsilonSquareLatticeIsAxialTreeBond
      (horizontalAboveAxisBond (spacing := spacing)) := by
  simp [epsilonSquareLatticeIsAxialTreeBond, horizontalAboveAxisBond]

/-- Reversal exchanges endpoints literally and is involutive. -/
theorem exact_reverse_involution
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    bond.reverse.source = bond.target ∧
      bond.reverse.target = bond.source ∧
      bond.reverse.reverse = bond :=
  ⟨rfl, rfl, bond.reverse_reverse⟩

/-- Reverse coordinates are forced to be inverses, not independent values. -/
theorem exact_configuration_reverse
    {G : Type*} [Group G]
    (configuration : EpsilonSquareLatticeConfiguration G spacing)
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    configuration bond.reverse = (configuration bond)⁻¹ :=
  configuration.reverse_value bond

/-- Every coordinate projection is measurable on the exact induced infinite carrier. -/
theorem exact_coordinate_measurable
    {G : Type*} [Group G] [MeasurableSpace G]
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Measurable (fun configuration : EpsilonSquareLatticeConfiguration G spacing =>
      configuration bond) :=
  EpsilonSquareLatticeConfiguration.measurable_apply bond

/-- Every coordinate projection is measurable on the exact induced axial carrier. -/
theorem exact_axial_coordinate_measurable
    {G : Type*} [Group G] [MeasurableSpace G]
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Measurable (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      configuration bond) :=
  EpsilonSquareLatticeAxialConfiguration.measurable_apply bond

/-- The exact infinite configuration carrier is constructively nonempty. -/
theorem configuration_nonempty {G : Type*} [Group G] :
    Nonempty (EpsilonSquareLatticeConfiguration G spacing) :=
  ⟨EpsilonSquareLatticeConfiguration.identity⟩

/-- The exact axial-gauge-fixed carrier is constructively nonempty. -/
theorem axialConfiguration_nonempty {G : Type*} [Group G] :
    Nonempty (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  ⟨EpsilonSquareLatticeAxialConfiguration.identity⟩

/-- The axial carrier has a concrete nonidentity off-axis coordinate. -/
theorem rowOneInteger_offAxis_nonidentity :
    EpsilonSquareLatticeAxialConfiguration.rowOneInteger
        (horizontalAboveAxisBond (spacing := spacing)) ≠ 1 := by
  norm_num [EpsilonSquareLatticeAxialConfiguration.rowOneInteger,
    horizontalAboveAxisBond]

/-- Consequently the axial carrier contains at least two distinct configurations. -/
theorem axialConfiguration_not_subsingleton :
    EpsilonSquareLatticeAxialConfiguration.rowOneInteger (spacing := spacing) ≠
      (EpsilonSquareLatticeAxialConfiguration.identity :
        EpsilonSquareLatticeAxialConfiguration (Multiplicative ℤ) spacing) := by
  intro equality
  have coordinateEquality := congrArg
    (fun configuration : EpsilonSquareLatticeAxialConfiguration (Multiplicative ℤ) spacing =>
      configuration (horizontalAboveAxisBond (spacing := spacing))) equality
  exact rowOneInteger_offAxis_nonidentity
    (coordinateEquality.trans
      (EpsilonSquareLatticeAxialConfiguration.identity_apply _))

/-- Every axial-tree coordinate is frozen to the identity in the same configuration. -/
theorem exact_axial_freezing
    {G : Type*} [Group G]
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (tree : epsilonSquareLatticeIsAxialTreeBond bond) :
    configuration bond = 1 :=
  configuration.axialTree_fixed bond tree

/-- A nonidentity claim on a tree coordinate is rejected. -/
theorem nonidentity_tree_value_blocked
    {G : Type*} [Group G]
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (tree : epsilonSquareLatticeIsAxialTreeBond bond)
    (claimed : configuration bond ≠ 1) : False :=
  claimed (configuration.axialTree_fixed bond tree)

/-- These carriers are explicitly two-dimensional and cannot be the Clay endpoint. -/
theorem infinite_lattice_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalInfiniteSquareLatticeConfiguration.Probes
