/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeFiniteVolumeBoundary

/-!
# Finite axial coordinates with a fixed Driver boundary condition

For Driver's gauge-fixed finite-volume law (7.2), only off-axis horizontal bonds in `Bₙ` are Haar
variables. Bonds in `Bₙᶜ` retain the supplied axial boundary configuration. This module constructs
the exact finite coordinate set and its measurable extension to the infinite axial carrier.

No action density, conditioned probability measure, or weak limit is constructed here.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

universe uG

/-- Off-axis rows in the inner square `Aₙ₋₁`. -/
def squareLatticeInnerOffAxisRows (radius : PositiveSquareLatticeBoxRadius) : Finset ℤ :=
  (Finset.Icc (-((radius.1 - 1 : ℕ) : ℤ)) ((radius.1 - 1 : ℕ) : ℤ)).erase 0

namespace squareLatticeInnerOffAxisRows

/-- Exact membership in the off-axis rows of `Aₙ₋₁`. -/
theorem mem_iff (radius : PositiveSquareLatticeBoxRadius) (row : ℤ) :
    row ∈ squareLatticeInnerOffAxisRows radius ↔
      -((radius.1 - 1 : ℕ) : ℤ) ≤ row ∧
        row ≤ ((radius.1 - 1 : ℕ) : ℤ) ∧ row ≠ 0 := by
  simp [squareLatticeInnerOffAxisRows]
  tauto

end squareLatticeInnerOffAxisRows

/-- Canonical right-directed off-axis horizontal sites among Driver's finite variables `Bₙ`. -/
def squareLatticeConditionedAxialCoordinateSites
    (radius : PositiveSquareLatticeBoxRadius) : Finset (ℤ × ℤ) :=
  (squareLatticeBoxInterval radius).product (squareLatticeInnerOffAxisRows radius)

/-- Exact finite independent axial coordinates for Driver's boundary-conditioned law. -/
def epsilonSquareLatticeConditionedAxialCoordinates
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Finset (EpsilonSquareLatticeDirectedBond spacing) :=
  (squareLatticeConditionedAxialCoordinateSites radius).image
    (epsilonSquareLatticeRightBond spacing)

/-- Coordinate subtype for the boundary-conditioned finite axial integral. -/
abbrev EpsilonSquareLatticeConditionedAxialCoordinate
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :=
  {bond : EpsilonSquareLatticeDirectedBond spacing //
    bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius}

namespace epsilonSquareLatticeConditionedAxialCoordinates

/-- A site in the exact horizontal and inner-row ranges supplies its canonical coordinate. -/
theorem mem_of_site
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : ℤ × ℤ)
    (horizontal : site.1 ∈ squareLatticeBoxInterval radius)
    (row : site.2 ∈ squareLatticeInnerOffAxisRows radius) :
    epsilonSquareLatticeRightBond spacing site ∈
      epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by
  apply Finset.mem_image.mpr
  exact ⟨site, Finset.mem_product.mpr ⟨horizontal, row⟩, rfl⟩

/-- Every conditioned coordinate is one of the larger free-box coordinates. -/
theorem subset_box
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    epsilonSquareLatticeConditionedAxialCoordinates spacing radius ⊆
      epsilonSquareLatticeBoxAxialCoordinates spacing radius := by
  intro bond membership
  simp only [epsilonSquareLatticeConditionedAxialCoordinates, Finset.mem_image] at membership
  obtain ⟨site, siteMembership, equality⟩ := membership
  subst bond
  rcases Finset.mem_product.mp siteMembership with ⟨horizontal, innerRow⟩
  apply epsilonSquareLatticeBoxAxialCoordinates.mem_of_site spacing radius site horizontal
  apply (squareLatticeBoxOffAxisRows.mem_iff radius site.2).mpr
  have bounds := (squareLatticeInnerOffAxisRows.mem_iff radius site.2).mp innerRow
  have positive : 1 ≤ radius.1 := radius.2
  exact ⟨by omega, by omega, bounds.2.2⟩

/-- Reverse orientations are never independent conditioned coordinates. -/
theorem reverse_not_mem
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius) :
    bond.reverse ∉ epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by
  intro reverseMembership
  exact epsilonSquareLatticeBoxAxialCoordinates.reverse_not_mem spacing radius bond
    (subset_box spacing radius membership)
    (subset_box spacing radius reverseMembership)

/-- Every conditioned coordinate is off Driver's axial tree. -/
theorem not_axial
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius) :
    ¬ epsilonSquareLatticeIsAxialTreeBond bond :=
  epsilonSquareLatticeBoxAxialCoordinates.not_axial spacing radius bond
    (subset_box spacing radius membership)

/-- Every conditioned coordinate is genuinely a bond of `Bₙ`. -/
theorem finiteVolume
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (membership : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius) :
    epsilonSquareLatticeFiniteVolumeBond spacing radius bond := by
  simp only [epsilonSquareLatticeConditionedAxialCoordinates, Finset.mem_image] at membership
  obtain ⟨site, siteMembership, equality⟩ := membership
  subst bond
  rcases Finset.mem_product.mp siteMembership with ⟨horizontal, rowMembership⟩
  have xBounds := (squareLatticeBoxInterval.mem_iff radius site.1).mp horizontal
  have yBounds := (squareLatticeInnerOffAxisRows.mem_iff radius site.2).mp rowMembership
  unfold epsilonSquareLatticeFiniteVolumeBond squareLatticeInnerClosedBoxPoint
  have positive : 1 ≤ radius.1 := radius.2
  simp [epsilonSquareLatticeRightBond]
  omega

/-- Every off-tree directed bond of `Bₙ` is represented in exactly one canonical orientation. -/
theorem finiteVolume_covered
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (finiteVolume : epsilonSquareLatticeFiniteVolumeBond spacing radius bond)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond) :
    bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius ∨
      bond.reverse ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by
  have nearest := bond.nearestNeighbor
  unfold SquareLatticeNearestNeighbor at nearest
  rcases nearest with horizontal | vertical
  · have sameRow : bond.target.2 = bond.source.2 := horizontal.2
    have rowNonzero : bond.source.2 ≠ 0 := by
      intro sourceZero
      apply notTree
      exact Or.inr ⟨sourceZero, by omega⟩
    unfold epsilonSquareLatticeFiniteVolumeBond at finiteVolume
    unfold squareLatticeInnerClosedBoxPoint at finiteVolume
    have positive : 1 ≤ radius.1 := radius.2
    rcases horizontal.1 with rightStep | leftStep
    · left
      have xBounds : -(radius.1 : ℤ) ≤ bond.source.1 ∧
          bond.source.1 < (radius.1 : ℤ) := by
        rcases finiteVolume with sourceInner | targetInner <;> omega
      have rowBounds : -((radius.1 - 1 : ℕ) : ℤ) ≤ bond.source.2 ∧
          bond.source.2 ≤ ((radius.1 - 1 : ℕ) : ℤ) := by
        rcases finiteVolume with sourceInner | targetInner <;> omega
      have membership := mem_of_site spacing radius bond.source
        ((squareLatticeBoxInterval.mem_iff radius bond.source.1).mpr xBounds)
        ((squareLatticeInnerOffAxisRows.mem_iff radius bond.source.2).mpr
          ⟨rowBounds.1, rowBounds.2, rowNonzero⟩)
      have equality : bond = epsilonSquareLatticeRightBond spacing bond.source := by
        apply EpsilonSquareLatticeDirectedBond.ext
        · rfl
        · apply Prod.ext <;> simp [epsilonSquareLatticeRightBond, rightStep, sameRow]
      rw [equality]
      exact membership
    · right
      have xBounds : -(radius.1 : ℤ) ≤ bond.target.1 ∧
          bond.target.1 < (radius.1 : ℤ) := by
        rcases finiteVolume with sourceInner | targetInner <;> omega
      have targetRowNonzero : bond.target.2 ≠ 0 := by omega
      have rowBounds : -((radius.1 - 1 : ℕ) : ℤ) ≤ bond.target.2 ∧
          bond.target.2 ≤ ((radius.1 - 1 : ℕ) : ℤ) := by
        rcases finiteVolume with sourceInner | targetInner <;> omega
      have membership := mem_of_site spacing radius bond.target
        ((squareLatticeBoxInterval.mem_iff radius bond.target.1).mpr xBounds)
        ((squareLatticeInnerOffAxisRows.mem_iff radius bond.target.2).mpr
          ⟨rowBounds.1, rowBounds.2, targetRowNonzero⟩)
      have equality : bond.reverse = epsilonSquareLatticeRightBond spacing bond.target := by
        apply EpsilonSquareLatticeDirectedBond.ext
        · rfl
        · apply Prod.ext <;> simp [epsilonSquareLatticeRightBond, leftStep, sameRow]
      rw [equality]
      exact membership
  · apply False.elim
    apply notTree
    exact Or.inl (by rcases vertical.1 with up | down <;> omega)

end epsilonSquareLatticeConditionedAxialCoordinates

namespace epsilonSquareLatticeFiniteVolumeBond

/-- Membership in `Bₙ` is invariant under bond reversal. -/
theorem reverse_iff
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    epsilonSquareLatticeFiniteVolumeBond spacing radius bond.reverse ↔
      epsilonSquareLatticeFiniteVolumeBond spacing radius bond := by
  simp [epsilonSquareLatticeFiniteVolumeBond, EpsilonSquareLatticeDirectedBond.reverse]
  tauto

end epsilonSquareLatticeFiniteVolumeBond

local instance conditionedAxialTreeDecidable
    (spacing : PositiveLatticeSpacing) (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Decidable (epsilonSquareLatticeIsAxialTreeBond bond) :=
  Classical.propDecidable _

/-- Extend finite Haar coordinates while retaining one fixed axial boundary configuration on `Bₙᶜ`. -/
def epsilonSquareLatticeConditionedAxialExtension
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G) :
    EpsilonSquareLatticeAxialConfiguration G spacing where
  configuration :=
    { value := fun bond =>
        if tree : epsilonSquareLatticeIsAxialTreeBond bond then 1
        else if forward : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius then
          configuration ⟨bond, forward⟩
        else if reverse : bond.reverse ∈
            epsilonSquareLatticeConditionedAxialCoordinates spacing radius then
          (configuration ⟨bond.reverse, reverse⟩)⁻¹
        else boundary bond
      reverse_value := by
        intro bond
        have treeReverse := epsilonSquareLatticeIsAxialTreeBond.reverse_iff bond
        by_cases tree : epsilonSquareLatticeIsAxialTreeBond bond
        · have reverseTree := treeReverse.mpr tree
          rw [dif_pos reverseTree, dif_pos tree]
          simp
        · have reverseNotTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond.reverse :=
            fun reverseTree => tree (treeReverse.mp reverseTree)
          by_cases forward : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius
          · have reverseAbsent := epsilonSquareLatticeConditionedAxialCoordinates.reverse_not_mem
              spacing radius bond forward
            have reverseReversePresent : bond.reverse.reverse ∈
                epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by simpa using forward
            rw [dif_neg reverseNotTree, dif_neg reverseAbsent, dif_pos reverseReversePresent,
              dif_neg tree, dif_pos forward]
            simp
          · by_cases reverse : bond.reverse ∈
                epsilonSquareLatticeConditionedAxialCoordinates spacing radius
            · rw [dif_neg reverseNotTree, dif_pos reverse, dif_neg tree, dif_neg forward,
                dif_pos reverse]
              simp
            · have reverseReverseAbsent : bond.reverse.reverse ∉
                  epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by simpa using forward
              rw [dif_neg reverseNotTree, dif_neg reverse, dif_neg reverseReverseAbsent,
                dif_neg tree, dif_neg forward, dif_neg reverse]
              exact boundary.configuration.reverse_value bond }
  axialTree_fixed := by
    intro bond tree
    change (if tree' : epsilonSquareLatticeIsAxialTreeBond bond then 1 else _) = 1
    rw [dif_pos tree]

namespace epsilonSquareLatticeConditionedAxialExtension

/-- Every selected finite coordinate is recovered exactly. -/
theorem coordinate
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius) :
    epsilonSquareLatticeConditionedAxialExtension spacing radius boundary configuration bond.1 =
      configuration bond := by
  have notTree := epsilonSquareLatticeConditionedAxialCoordinates.not_axial
    spacing radius bond.1 bond.2
  change (if tree : epsilonSquareLatticeIsAxialTreeBond bond.1 then 1
    else if forward : bond.1 ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius then
      configuration ⟨bond.1, forward⟩ else _) = configuration bond
  rw [dif_neg notTree, dif_pos bond.2]

/-- The extension agrees exactly with the supplied boundary condition on every bond of `Bₙᶜ`. -/
theorem boundary
    {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing)
    (configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (outside : epsilonSquareLatticeBoundaryConditionBond spacing radius bond) :
    epsilonSquareLatticeConditionedAxialExtension spacing radius boundary configuration bond =
      boundary bond := by
  by_cases tree : epsilonSquareLatticeIsAxialTreeBond bond
  · change (if tree' : epsilonSquareLatticeIsAxialTreeBond bond then 1 else _) = boundary bond
    rw [dif_pos tree, boundary.axialTree_fixed bond tree]
  · have forward : bond ∉ epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by
      intro membership
      exact outside (epsilonSquareLatticeConditionedAxialCoordinates.finiteVolume
        spacing radius bond membership)
    have reverse : bond.reverse ∉ epsilonSquareLatticeConditionedAxialCoordinates spacing radius := by
      intro membership
      apply outside
      exact (epsilonSquareLatticeFiniteVolumeBond.reverse_iff spacing radius bond).mp
        (epsilonSquareLatticeConditionedAxialCoordinates.finiteVolume
          spacing radius bond.reverse membership)
    change (if tree' : epsilonSquareLatticeIsAxialTreeBond bond then 1
      else if forward' : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius then _
      else if reverse' : bond.reverse ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius
      then _ else boundary bond) = boundary bond
    rw [dif_neg tree, dif_neg forward, dif_neg reverse]

/-- The conditioned extension is measurable in its finite coordinate argument. -/
theorem measurable
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (boundary : EpsilonSquareLatticeAxialConfiguration G spacing) :
    Measurable (epsilonSquareLatticeConditionedAxialExtension spacing radius boundary) := by
  apply (measurable_comap_iff
    (g := EpsilonSquareLatticeAxialConfiguration.configuration)).mpr
  apply (measurable_comap_iff (g := EpsilonSquareLatticeConfiguration.value)).mpr
  apply measurable_pi_iff.mpr
  intro bond
  by_cases tree : epsilonSquareLatticeIsAxialTreeBond bond
  · simp [epsilonSquareLatticeConditionedAxialExtension, tree]
  · by_cases forward : bond ∈ epsilonSquareLatticeConditionedAxialCoordinates spacing radius
    · have evaluation : Measurable
          (fun configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G =>
            configuration ⟨bond, forward⟩) :=
        measurable_pi_apply (⟨bond, forward⟩ :
          EpsilonSquareLatticeConditionedAxialCoordinate spacing radius)
      simpa [epsilonSquareLatticeConditionedAxialExtension, tree, forward] using evaluation
    · by_cases reverse : bond.reverse ∈
          epsilonSquareLatticeConditionedAxialCoordinates spacing radius
      · have evaluation : Measurable
            (fun configuration : EpsilonSquareLatticeConditionedAxialCoordinate spacing radius → G =>
              (configuration ⟨bond.reverse, reverse⟩)⁻¹) :=
          (measurable_pi_apply (⟨bond.reverse, reverse⟩ :
            EpsilonSquareLatticeConditionedAxialCoordinate spacing radius)).inv
        simpa [epsilonSquareLatticeConditionedAxialExtension, tree, forward, reverse] using evaluation
      · simp [epsilonSquareLatticeConditionedAxialExtension, tree, forward, reverse]

end epsilonSquareLatticeConditionedAxialExtension

end

end YangMills.Dimensions
