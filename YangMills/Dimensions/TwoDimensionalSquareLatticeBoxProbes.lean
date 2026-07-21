/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBox

/-!
# Probes for exact finite square boxes
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBox.Probes

noncomputable section

variable {spacing : PositiveLatticeSpacing}

/-- The smallest allowed positive box radius. -/
def radiusOne : PositiveSquareLatticeBoxRadius :=
  ⟨1, by decide⟩

/-- Radius two strictly extends the smallest box. -/
def radiusTwo : PositiveSquareLatticeBoxRadius :=
  ⟨2, by decide⟩

/-- Box plaquettes and independent coordinates are literally nested with radius. -/
theorem exact_radius_nesting :
    epsilonSquareLatticeBoxPlaquettes spacing radiusOne ⊆
        epsilonSquareLatticeBoxPlaquettes spacing radiusTwo ∧
      epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne ⊆
        epsilonSquareLatticeBoxAxialCoordinates spacing radiusTwo :=
  ⟨epsilonSquareLatticeBoxPlaquettes.mono spacing (by decide),
    epsilonSquareLatticeBoxAxialCoordinates.mono spacing (by decide)⟩

/-- The origin plaquette belongs to the side-`2ε` box. -/
theorem origin_plaquette_mem :
    (⟨(0, 0)⟩ : EpsilonSquareLatticePlaquette spacing) ∈
      epsilonSquareLatticeBoxPlaquettes spacing radiusOne := by
  apply (epsilonSquareLatticeBoxPlaquettes.mem_iff spacing radiusOne _).mpr
  change (-1 : ℤ) ≤ 0 ∧ 0 < 1 ∧ (-1 : ℤ) ≤ 0 ∧ 0 < 1
  norm_num

/-- A plaquette beyond the positive box boundary is rejected. -/
theorem outside_plaquette_not_mem :
    (⟨(1, 0)⟩ : EpsilonSquareLatticePlaquette spacing) ∉
      epsilonSquareLatticeBoxPlaquettes spacing radiusOne := by
  intro membership
  have bounds := (epsilonSquareLatticeBoxPlaquettes.mem_iff spacing radiusOne _).mp membership
  change (-1 : ℤ) ≤ 1 ∧ 1 < 1 ∧ (-1 : ℤ) ≤ 0 ∧ 0 < 1 at bounds
  omega

/-- The off-axis right-directed row-one bond is an independent radius-one coordinate. -/
theorem rowOne_coordinate_mem :
    epsilonSquareLatticeRightBond spacing (0, 1) ∈
      epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne := by
  apply epsilonSquareLatticeBoxAxialCoordinates.mem_of_site
  · apply (squareLatticeBoxInterval.mem_iff radiusOne 0).mpr
    change (-1 : ℤ) ≤ 0 ∧ 0 < 1
    norm_num
  · apply (squareLatticeBoxOffAxisRows.mem_iff radiusOne 1).mpr
    change (-1 : ℤ) ≤ 1 ∧ 1 ≤ 1 ∧ (1 : ℤ) ≠ 0
    norm_num

/-- The physical half-extent remains definitionally the exact product `nε`. -/
theorem exact_physical_halfExtent :
    epsilonSquareLatticeBoxHalfExtent spacing radiusOne = spacing.1 * radiusOne.1 :=
  rfl

/-- The reverse/left-directed orientation is not stored as an independent coordinate. -/
theorem leftDirected_coordinate_not_mem :
    (epsilonSquareLatticeRightBond spacing (0, 1)).reverse ∉
      epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne := by
  intro membership
  simp only [epsilonSquareLatticeBoxAxialCoordinates, Finset.mem_image] at membership
  obtain ⟨site, _, equality⟩ := membership
  have sourceEquality := congrArg EpsilonSquareLatticeDirectedBond.source equality
  have targetEquality := congrArg EpsilonSquareLatticeDirectedBond.target equality
  have sourceFirst := congrArg Prod.fst sourceEquality
  have targetFirst := congrArg Prod.fst targetEquality
  simp [epsilonSquareLatticeRightBond] at sourceFirst targetFirst
  omega

/-- Horizontal x-axis bonds are excluded from independent coordinates because axial gauge freezes
them. -/
theorem xAxis_coordinate_not_mem :
    epsilonSquareLatticeRightBond spacing (0, 0) ∉
      epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne := by
  intro membership
  exact (epsilonSquareLatticeBoxAxialCoordinates.not_axial spacing radiusOne _ membership)
    (Or.inr ⟨rfl, rfl⟩)

/-- Every boundary bond of every selected box plaquette is either axial or represented in one of the
two coordinate orientations. -/
theorem exact_box_boundary_coverage
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (plaquetteMembership : plaquette ∈
      epsilonSquareLatticeBoxPlaquettes spacing radiusOne)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (boundaryMembership : bond ∈ plaquette.boundaryBonds) :
    epsilonSquareLatticeIsAxialTreeBond bond ∨
      bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne ∨
      bond.reverse ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne :=
  epsilonSquareLatticeBoxAxialCoordinates.plaquette_boundary_covered
    spacing radiusOne plaquette plaquetteMembership bond boundaryMembership

/-- A disconnected non-tree plaquette boundary is impossible in the exact box geometry. -/
theorem disconnected_box_boundary_blocked
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (plaquetteMembership : plaquette ∈
      epsilonSquareLatticeBoxPlaquettes spacing radiusOne)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (boundaryMembership : bond ∈ plaquette.boundaryBonds)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (forwardAbsent : bond ∉ epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne)
    (reverseAbsent : bond.reverse ∉
      epsilonSquareLatticeBoxAxialCoordinates spacing radiusOne) : False := by
  rcases exact_box_boundary_coverage plaquette plaquetteMembership bond boundaryMembership with
    tree | forward | reverse
  · exact notTree tree
  · exact forwardAbsent forward
  · exact reverseAbsent reverse

/-- Zero radius cannot instantiate the public box-radius carrier. -/
theorem zero_radius_blocked (claimed : PositiveSquareLatticeBoxRadius)
    (zero : claimed.1 = 0) : False := by
  have positive := claimed.2
  omega

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBox.Probes
