/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialExtension

/-!
# Probes for conditioned finite axial extensions
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialExtension.Probes

noncomputable section

universe uG

/-- Radius two has a genuinely off-axis inner row. -/
def radiusTwo : PositiveSquareLatticeBoxRadius := ⟨2, by decide⟩

/-- A canonical row-one coordinate is present at radius two. -/
theorem row_one_coordinate_present (spacing : PositiveLatticeSpacing) :
    epsilonSquareLatticeRightBond spacing (0, 1) ∈
      epsilonSquareLatticeConditionedAxialCoordinates spacing radiusTwo := by
  apply Finset.mem_image.mpr
  refine ⟨(0, 1), ?_, rfl⟩
  apply Finset.mem_product.mpr
  constructor
  · apply (squareLatticeBoxInterval.mem_iff radiusTwo 0).mpr
    have positive := radiusTwo.2
    constructor <;> omega
  · apply (squareLatticeInnerOffAxisRows.mem_iff radiusTwo 1).mpr
    refine ⟨?_, ?_, by norm_num⟩
    · change (-1 : ℤ) ≤ 1
      norm_num
    · change (1 : ℤ) ≤ 1
      norm_num

/-- Both horizontal endpoint ranges occur; the left boundary source is not accidentally omitted. -/
theorem horizontal_endpoint_coordinates_present (spacing : PositiveLatticeSpacing) :
    epsilonSquareLatticeRightBond spacing (-2, 1) ∈
        epsilonSquareLatticeConditionedAxialCoordinates spacing radiusTwo ∧
      epsilonSquareLatticeRightBond spacing (1, 1) ∈
        epsilonSquareLatticeConditionedAxialCoordinates spacing radiusTwo := by
  constructor
  · apply epsilonSquareLatticeConditionedAxialCoordinates.mem_of_site spacing radiusTwo (-2, 1)
    · apply (squareLatticeBoxInterval.mem_iff radiusTwo (-2)).mpr
      change (-(2 : ℤ) ≤ -2 ∧ (-2 : ℤ) < 2)
      omega
    · apply (squareLatticeInnerOffAxisRows.mem_iff radiusTwo 1).mpr
      change (-(1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≠ 0)
      norm_num
  · apply epsilonSquareLatticeConditionedAxialCoordinates.mem_of_site spacing radiusTwo (1, 1)
    · apply (squareLatticeBoxInterval.mem_iff radiusTwo 1).mpr
      change (-(2 : ℤ) ≤ 1 ∧ (1 : ℤ) < 2)
      omega
    · apply (squareLatticeInnerOffAxisRows.mem_iff radiusTwo 1).mpr
      change (-(1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≠ 0)
      norm_num

/-- Conditioned coordinates are finite variables, off-tree, and reverse-disjoint. -/
theorem coordinate_contract
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius) :
    epsilonSquareLatticeFiniteVolumeBond spacing radius bond ∧
      ¬ epsilonSquareLatticeIsAxialTreeBond bond ∧
      bond.reverse ∉ epsilonSquareLatticeConditionedAxialCoordinates spacing radius :=
  ⟨epsilonSquareLatticeConditionedAxialCoordinates.finiteVolume spacing radius bond membership,
    epsilonSquareLatticeConditionedAxialCoordinates.not_axial spacing radius bond membership,
    epsilonSquareLatticeConditionedAxialCoordinates.reverse_not_mem spacing radius bond membership⟩

/-- Conversely, every off-tree bond of `Bₙ` is covered in forward or reverse orientation. -/
theorem exact_finite_volume_coverage
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (finiteVolume : epsilonSquareLatticeFiniteVolumeBond spacing radius bond)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond) :
    bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius ∨
      bond.reverse ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius :=
  epsilonSquareLatticeConditionedAxialCoordinates.finiteVolume_covered
    spacing radius bond finiteVolume notTree

/-- Omitting both orientations of one off-tree finite bond is hostilely impossible. -/
theorem omitted_finite_coordinate_blocked
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (finiteVolume : epsilonSquareLatticeFiniteVolumeBond spacing radius bond)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (forwardAbsent : bond ∉ epsilonSquareLatticeConditionedAxialCoordinates spacing radius)
    (reverseAbsent : bond.reverse ∉ epsilonSquareLatticeConditionedAxialCoordinates spacing radius) :
    False := by
  rcases epsilonSquareLatticeConditionedAxialCoordinates.finiteVolume_covered
    spacing radius bond finiteVolume notTree with forward | reverse
  · exact forwardAbsent forward
  · exact reverseAbsent reverse

/-- Every finite coordinate is recovered exactly. -/
theorem exact_coordinate_recovery
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius) :
    epsilonSquareLatticeConditionedAxialExtension spacing radius boundary configuration bond.1 =
      configuration bond :=
  epsilonSquareLatticeConditionedAxialExtension.coordinate
    spacing radius boundary configuration bond

/-- Every bond in `Bₙᶜ` retains the supplied boundary value exactly. -/
theorem exact_boundary_recovery
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (outside : epsilonSquareLatticeBoundaryConditionBond spacing radius bond) :
    epsilonSquareLatticeConditionedAxialExtension spacing radius boundary configuration bond =
      boundary bond :=
  epsilonSquareLatticeConditionedAxialExtension.boundary
    spacing radius boundary configuration bond outside

/-- A nonidentity boundary value cannot be silently replaced by the free identity extension. -/
theorem nonidentity_boundary_survives
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (outside : epsilonSquareLatticeBoundaryConditionBond spacing radius bond)
    (nonidentity : boundary bond ≠ 1) :
    epsilonSquareLatticeConditionedAxialExtension spacing radius boundary configuration bond ≠ 1 := by
  rw [epsilonSquareLatticeConditionedAxialExtension.boundary
    spacing radius boundary configuration bond outside]
  exact nonidentity

/-- The extension is measurable in all finite Haar coordinates. -/
theorem exact_extension_measurable
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing) :
    Measurable (epsilonSquareLatticeConditionedAxialExtension spacing radius boundary) :=
  epsilonSquareLatticeConditionedAxialExtension.measurable spacing radius boundary

/-- Conditioned geometry remains strictly two-dimensional. -/
theorem conditioned_extension_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeConditionedAxialExtension.Probes
