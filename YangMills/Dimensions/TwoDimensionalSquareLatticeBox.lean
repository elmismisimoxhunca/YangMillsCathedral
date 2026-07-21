/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticePlaquetteAction
import Mathlib.Data.Int.Interval

/-!
# Exact finite square boxes in the scaled square lattice

Driver §7 uses closed squares of side `2n` centered at the origin and their elementary plaquettes.
At spacing `ε`, this module defines the exact integer lower-left plaquette indices and the independent
right-directed off-axis horizontal bonds for the axial gauge. This is finite geometry only; no
presentation extension, action measure, boundary condition, limit, or convergence is constructed.
-/

namespace YangMills.Dimensions

noncomputable section

/-- A strictly positive square-box radius. -/
abbrev PositiveSquareLatticeBoxRadius := {radius : ℕ // 0 < radius}

/-- Integer coordinates from `-n` through `n-1`, indexing `2n` elementary intervals. -/
def squareLatticeBoxInterval (radius : PositiveSquareLatticeBoxRadius) : Finset ℤ :=
  Finset.Icc (-(radius.1 : ℤ)) ((radius.1 : ℤ) - 1)

/-- Integer vertex rows from `-n` through `n`, excluding the axial row zero. -/
def squareLatticeBoxOffAxisRows (radius : PositiveSquareLatticeBoxRadius) : Finset ℤ :=
  (Finset.Icc (-(radius.1 : ℤ)) (radius.1 : ℤ)).erase 0

/-- Lower-left integer sites of every elementary plaquette in the closed side-`2nε` box. -/
def squareLatticeBoxPlaquetteSites (radius : PositiveSquareLatticeBoxRadius) :
    Finset (ℤ × ℤ) :=
  (squareLatticeBoxInterval radius).product (squareLatticeBoxInterval radius)

/-- Right-directed off-axis horizontal bond source sites, the independent axial coordinates. -/
def squareLatticeBoxAxialCoordinateSites (radius : PositiveSquareLatticeBoxRadius) :
    Finset (ℤ × ℤ) :=
  (squareLatticeBoxInterval radius).product (squareLatticeBoxOffAxisRows radius)

/-- Every selected source site determines its actual elementary plaquette. -/
def epsilonSquareLatticeBoxPlaquettes
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Finset (EpsilonSquareLatticePlaquette spacing) :=
  (squareLatticeBoxPlaquetteSites radius).image fun site => ⟨site⟩

/-- Right-directed horizontal nearest-neighbor bond from one integer source site. -/
def epsilonSquareLatticeRightBond
    (spacing : PositiveLatticeSpacing) (site : ℤ × ℤ) :
    EpsilonSquareLatticeDirectedBond spacing where
  source := site
  target := (site.1 + 1, site.2)
  nearestNeighbor := Or.inl ⟨Or.inl rfl, rfl⟩

/-- Exact finite independent off-axis axial bond coordinates in the box. -/
def epsilonSquareLatticeBoxAxialCoordinates
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Finset (EpsilonSquareLatticeDirectedBond spacing) :=
  (squareLatticeBoxAxialCoordinateSites radius).image
    (epsilonSquareLatticeRightBond spacing)

/-- Physical half-extent `nε` of the centered box. -/
def epsilonSquareLatticeBoxHalfExtent
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) : ℝ :=
  spacing.1 * radius.1

namespace squareLatticeBoxInterval

/-- Exact integer membership in the `2n` interval. -/
theorem mem_iff (radius : PositiveSquareLatticeBoxRadius) (coordinate : ℤ) :
    coordinate ∈ squareLatticeBoxInterval radius ↔
      -(radius.1 : ℤ) ≤ coordinate ∧ coordinate < (radius.1 : ℤ) := by
  simp [squareLatticeBoxInterval]

end squareLatticeBoxInterval

namespace squareLatticeBoxOffAxisRows

/-- Exact integer membership in the `2n` nonzero vertex rows. -/
theorem mem_iff (radius : PositiveSquareLatticeBoxRadius) (row : ℤ) :
    row ∈ squareLatticeBoxOffAxisRows radius ↔
      -(radius.1 : ℤ) ≤ row ∧ row ≤ (radius.1 : ℤ) ∧ row ≠ 0 := by
  simp [squareLatticeBoxOffAxisRows]
  tauto

end squareLatticeBoxOffAxisRows

namespace epsilonSquareLatticeBoxPlaquettes

/-- Membership is exactly the expected pair of lower-left integer bounds. -/
theorem mem_iff
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius ↔
      -(radius.1 : ℤ) ≤ plaquette.lowerLeft.1 ∧
        plaquette.lowerLeft.1 < (radius.1 : ℤ) ∧
      -(radius.1 : ℤ) ≤ plaquette.lowerLeft.2 ∧
        plaquette.lowerLeft.2 < (radius.1 : ℤ) := by
  constructor
  · intro membership
    simp only [epsilonSquareLatticeBoxPlaquettes, Finset.mem_image] at membership
    obtain ⟨site, siteMembership, equality⟩ := membership
    have lowerLeft : site = plaquette.lowerLeft := by
      simpa using congrArg EpsilonSquareLatticePlaquette.lowerLeft equality
    subst site
    have paired :
        (-(radius.1 : ℤ) ≤ plaquette.lowerLeft.1 ∧
          plaquette.lowerLeft.1 < (radius.1 : ℤ)) ∧
        (-(radius.1 : ℤ) ≤ plaquette.lowerLeft.2 ∧
          plaquette.lowerLeft.2 < (radius.1 : ℤ)) := by
      simpa [squareLatticeBoxPlaquetteSites, squareLatticeBoxInterval.mem_iff] using siteMembership
    exact ⟨paired.1.1, paired.1.2, paired.2.1, paired.2.2⟩
  · intro bounds
    apply Finset.mem_image.mpr
    refine ⟨plaquette.lowerLeft, ?_, ?_⟩
    · rcases bounds with ⟨xLower, xUpper, yLower, yUpper⟩
      simpa [squareLatticeBoxPlaquetteSites, squareLatticeBoxInterval.mem_iff] using
        And.intro (And.intro xLower xUpper) (And.intro yLower yUpper)
    · cases plaquette
      rfl

/-- Increasing the radius literally includes the smaller plaquette set. -/
theorem mono
    (spacing : PositiveLatticeSpacing)
    {smaller larger : PositiveSquareLatticeBoxRadius}
    (radius_le : smaller.1 ≤ larger.1) :
    epsilonSquareLatticeBoxPlaquettes spacing smaller ⊆
      epsilonSquareLatticeBoxPlaquettes spacing larger := by
  intro plaquette membership
  have bounds := (mem_iff spacing smaller plaquette).mp membership
  apply (mem_iff spacing larger plaquette).mpr
  have castRadius : (smaller.1 : ℤ) ≤ (larger.1 : ℤ) := by exact_mod_cast radius_le
  omega

end epsilonSquareLatticeBoxPlaquettes

namespace epsilonSquareLatticeBoxAxialCoordinates

/-- Membership is exactly a right-directed bond whose source is in the horizontal interval and on a
nonzero vertex row inside the box. -/
theorem mem_of_site
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : ℤ × ℤ)
    (horizontal : site.1 ∈ squareLatticeBoxInterval radius)
    (row : site.2 ∈ squareLatticeBoxOffAxisRows radius) :
    epsilonSquareLatticeRightBond spacing site ∈
      epsilonSquareLatticeBoxAxialCoordinates spacing radius := by
  apply Finset.mem_image.mpr
  exact ⟨site, Finset.mem_product.mpr ⟨horizontal, row⟩, rfl⟩

/-- Increasing the radius literally includes the smaller independent-coordinate set. -/
theorem mono
    (spacing : PositiveLatticeSpacing)
    {smaller larger : PositiveSquareLatticeBoxRadius}
    (radius_le : smaller.1 ≤ larger.1) :
    epsilonSquareLatticeBoxAxialCoordinates spacing smaller ⊆
      epsilonSquareLatticeBoxAxialCoordinates spacing larger := by
  intro bond membership
  simp only [epsilonSquareLatticeBoxAxialCoordinates, Finset.mem_image] at membership ⊢
  obtain ⟨site, siteMembership, equality⟩ := membership
  refine ⟨site, ?_, equality⟩
  rcases Finset.mem_product.mp siteMembership with ⟨horizontal, row⟩
  apply Finset.mem_product.mpr
  have castRadius : (smaller.1 : ℤ) ≤ (larger.1 : ℤ) := by exact_mod_cast radius_le
  constructor
  · apply (squareLatticeBoxInterval.mem_iff larger site.1).mpr
    have smallBounds := (squareLatticeBoxInterval.mem_iff smaller site.1).mp horizontal
    omega
  · apply (squareLatticeBoxOffAxisRows.mem_iff larger site.2).mpr
    have smallBounds := (squareLatticeBoxOffAxisRows.mem_iff smaller site.2).mp row
    exact ⟨by omega, by omega, smallBounds.2.2⟩

/-- Every box coordinate is genuinely off Driver's axial tree. -/
theorem not_axial
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius) :
    ¬ epsilonSquareLatticeIsAxialTreeBond bond := by
  simp only [epsilonSquareLatticeBoxAxialCoordinates, Finset.mem_image] at membership
  obtain ⟨site, siteMembership, equality⟩ := membership
  subst bond
  have rowMembership := (Finset.mem_product.mp siteMembership).2
  have rowNonzero := (squareLatticeBoxOffAxisRows.mem_iff radius site.2).mp rowMembership |>.2.2
  simp [epsilonSquareLatticeIsAxialTreeBond, epsilonSquareLatticeRightBond, rowNonzero]

/-- Every non-tree boundary bond of every box plaquette is one of the selected independent
coordinates, in its forward or reverse orientation. -/
theorem plaquette_boundary_covered
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (plaquette : EpsilonSquareLatticePlaquette spacing)
    (plaquetteMembership : plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (boundaryMembership : bond ∈ plaquette.boundaryBonds) :
    epsilonSquareLatticeIsAxialTreeBond bond ∨
      bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius ∨
      bond.reverse ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius := by
  have bounds := (epsilonSquareLatticeBoxPlaquettes.mem_iff spacing radius plaquette).mp
    plaquetteMembership
  simp [EpsilonSquareLatticePlaquette.boundaryBonds] at boundaryMembership
  rcases boundaryMembership with bottom | right | top | left
  · subst bond
    by_cases axis : plaquette.lowerLeft.2 = 0
    · exact Or.inl (Or.inr ⟨axis, axis⟩)
    · right
      left
      apply mem_of_site spacing radius plaquette.lowerLeft
      · exact (squareLatticeBoxInterval.mem_iff radius _).mpr ⟨bounds.1, bounds.2.1⟩
      · apply (squareLatticeBoxOffAxisRows.mem_iff radius _).mpr
        exact ⟨bounds.2.2.1, by omega, axis⟩
  · subst bond
    exact Or.inl (Or.inl rfl)
  · subst bond
    by_cases axis : plaquette.lowerLeft.2 + 1 = 0
    · exact Or.inl (Or.inr ⟨axis, axis⟩)
    · right
      right
      have coordinateMembership := mem_of_site spacing radius
        (plaquette.lowerLeft.1, plaquette.lowerLeft.2 + 1)
        ((squareLatticeBoxInterval.mem_iff radius _).mpr ⟨bounds.1, bounds.2.1⟩)
        ((squareLatticeBoxOffAxisRows.mem_iff radius _).mpr
          ⟨by omega, by omega, axis⟩)
      have equality : plaquette.topBond.reverse =
          epsilonSquareLatticeRightBond spacing
            (plaquette.lowerLeft.1, plaquette.lowerLeft.2 + 1) := by
        ext <;> rfl
      simpa [equality] using coordinateMembership
  · subst bond
    exact Or.inl (Or.inl rfl)

end epsilonSquareLatticeBoxAxialCoordinates

end

end YangMills.Dimensions
