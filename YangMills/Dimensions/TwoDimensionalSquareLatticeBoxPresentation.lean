/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBox
import YangMills.Dimensions.TwoDimensionalFiniteAxialPlaquetteMeasure

/-!
# Exact square-box finite axial presentations

This module adapts the concrete finite square-box coordinate and plaquette sets to the generic finite
axial presentation carrier. Arbitrary finite coordinate values are extended by inversion on reverse
bonds and by the identity on every other bond. This constructs geometry and a measurable extension,
not a partition-function certificate, probability measure, boundary limit, or continuum limit.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

/-- Independent coordinate subtype of the exact axial square box. -/
abbrev EpsilonSquareLatticeBoxCoordinate :=
  {bond : EpsilonSquareLatticeDirectedBond spacing //
    bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius}

/-- Plaquette subtype of the exact square box. -/
abbrev EpsilonSquareLatticeBoxPlaquette :=
  {plaquette : EpsilonSquareLatticePlaquette spacing //
    plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing radius}

local instance axialTreeDecidable
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Decidable (epsilonSquareLatticeIsAxialTreeBond bond) :=
  Classical.propDecidable _

/-- Extend arbitrary finite box coordinates to the exact infinite axial carrier. -/
def epsilonSquareLatticeBoxAxialExtension
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G) :
    EpsilonSquareLatticeAxialConfiguration G spacing where
  configuration :=
    { value := fun bond =>
        if tree : epsilonSquareLatticeIsAxialTreeBond bond then 1
        else if forward : bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
          configuration ⟨bond, forward⟩
        else if reverse : bond.reverse ∈
            epsilonSquareLatticeBoxAxialCoordinates spacing radius then
          (configuration ⟨bond.reverse, reverse⟩)⁻¹
        else 1
      reverse_value := by
        intro bond
        have treeReverse := epsilonSquareLatticeIsAxialTreeBond.reverse_iff bond
        by_cases tree : epsilonSquareLatticeIsAxialTreeBond bond
        · have reverseTree : epsilonSquareLatticeIsAxialTreeBond bond.reverse := treeReverse.mpr tree
          rw [dif_pos reverseTree, dif_pos tree]
          simp
        · have reverseNotTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond.reverse := by
            exact fun reverseTree => tree (treeReverse.mp reverseTree)
          by_cases forward : bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius
          · have reverseAbsent := epsilonSquareLatticeBoxAxialCoordinates.reverse_not_mem
              spacing radius bond forward
            have reverseReversePresent : bond.reverse.reverse ∈
                epsilonSquareLatticeBoxAxialCoordinates spacing radius := by
              simpa using forward
            rw [dif_neg reverseNotTree, dif_neg reverseAbsent, dif_pos reverseReversePresent,
              dif_neg tree, dif_pos forward]
            simp
          · by_cases reverse : bond.reverse ∈
                epsilonSquareLatticeBoxAxialCoordinates spacing radius
            · rw [dif_neg reverseNotTree, dif_pos reverse, dif_neg tree, dif_neg forward,
                dif_pos reverse]
              simp
            · have reverseReverseAbsent : bond.reverse.reverse ∉
                  epsilonSquareLatticeBoxAxialCoordinates spacing radius := by
                simpa using forward
              rw [dif_neg reverseNotTree, dif_neg reverse, dif_neg reverseReverseAbsent,
                dif_neg tree, dif_neg forward, dif_neg reverse]
              simp }
  axialTree_fixed := by
    intro bond tree
    change (if tree' : epsilonSquareLatticeIsAxialTreeBond bond then 1
      else if forward : bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
        configuration ⟨bond, forward⟩
      else if reverse : bond.reverse ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
        (configuration ⟨bond.reverse, reverse⟩)⁻¹ else 1) = 1
    rw [dif_pos tree]

namespace epsilonSquareLatticeBoxAxialExtension

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Every selected coordinate is recovered exactly. -/
theorem coordinate
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeBoxCoordinate spacing radius) :
    epsilonSquareLatticeBoxAxialExtension spacing radius configuration bond.1 =
      configuration bond := by
  have notTree := epsilonSquareLatticeBoxAxialCoordinates.not_axial
    spacing radius bond.1 bond.2
  change (if tree : epsilonSquareLatticeIsAxialTreeBond bond.1 then 1
    else if forward : bond.1 ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
      configuration ⟨bond.1, forward⟩
    else if reverse : bond.1.reverse ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
      (configuration ⟨bond.1.reverse, reverse⟩)⁻¹ else 1) = configuration bond
  rw [dif_neg notTree, dif_pos bond.2]

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Every unrepresented off-tree bond is set to the identity. -/
theorem unrepresented
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond)
    (forward : bond ∉ epsilonSquareLatticeBoxAxialCoordinates spacing radius)
    (reverse : bond.reverse ∉ epsilonSquareLatticeBoxAxialCoordinates spacing radius) :
    epsilonSquareLatticeBoxAxialExtension spacing radius configuration bond = 1 := by
  change (if tree : epsilonSquareLatticeIsAxialTreeBond bond then 1
    else if forward : bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
      configuration ⟨bond, forward⟩
    else if reverse : bond.reverse ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius then
      (configuration ⟨bond.reverse, reverse⟩)⁻¹ else 1) = 1
  rw [dif_neg notTree, dif_neg forward, dif_neg reverse]

/-- The exact box extension is measurable. -/
theorem measurable :
    Measurable (epsilonSquareLatticeBoxAxialExtension (G := G) spacing radius) := by
  apply (measurable_comap_iff
    (g := EpsilonSquareLatticeAxialConfiguration.configuration)).mpr
  apply (measurable_comap_iff
    (g := EpsilonSquareLatticeConfiguration.value)).mpr
  apply measurable_pi_iff.mpr
  intro bond
  by_cases tree : epsilonSquareLatticeIsAxialTreeBond bond
  · simp [epsilonSquareLatticeBoxAxialExtension, tree]
  · by_cases forward : bond ∈ epsilonSquareLatticeBoxAxialCoordinates spacing radius
    · have evaluation : Measurable
          (fun configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G =>
            configuration (⟨bond, forward⟩ :
              EpsilonSquareLatticeBoxCoordinate spacing radius)) :=
        measurable_pi_apply (⟨bond, forward⟩ :
          EpsilonSquareLatticeBoxCoordinate spacing radius)
      simpa [epsilonSquareLatticeBoxAxialExtension, tree, forward] using evaluation
    · by_cases reverse : bond.reverse ∈
          epsilonSquareLatticeBoxAxialCoordinates spacing radius
      · have evaluation : Measurable
            (fun configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G =>
              (configuration (⟨bond.reverse, reverse⟩ :
                EpsilonSquareLatticeBoxCoordinate spacing radius))⁻¹) :=
          (measurable_pi_apply (⟨bond.reverse, reverse⟩ :
            EpsilonSquareLatticeBoxCoordinate spacing radius)).inv
        simpa [epsilonSquareLatticeBoxAxialExtension, tree, forward, reverse] using evaluation
      · simp [epsilonSquareLatticeBoxAxialExtension, tree, forward, reverse]

end epsilonSquareLatticeBoxAxialExtension

/-- Horizontal axial value on the right-directed bond at an arbitrary integer site. Values on the
axis and outside the finite coordinate set are inherited exactly from the box extension. -/
def epsilonSquareLatticeBoxHorizontalValue
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (site : ℤ × ℤ) : G :=
  epsilonSquareLatticeBoxAxialExtension spacing radius configuration
    (epsilonSquareLatticeRightBond spacing site)

namespace EpsilonSquareLatticePlaquette

omit [MeasurableSpace G] [MeasurableInv G] in
/-- A plaquette bottom edge is the right-directed horizontal bond at its lower-left site. -/
@[simp] theorem bottomBond_eq_rightBond
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette.bottomBond = epsilonSquareLatticeRightBond spacing plaquette.lowerLeft := by
  ext <;> rfl

omit [MeasurableSpace G] [MeasurableInv G] in
/-- A plaquette top traversal is the reverse of the right-directed bond on its upper row. -/
@[simp] theorem topBond_eq_reverse_rightBond
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    plaquette.topBond =
      (epsilonSquareLatticeRightBond spacing
        (plaquette.lowerLeft.1, plaquette.lowerLeft.2 + 1)).reverse := by
  ext <;> rfl

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Every vertical right edge lies in Driver's axial tree. -/
theorem rightBond_isAxialTree
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeIsAxialTreeBond plaquette.rightBond :=
  Or.inl rfl

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Every vertical left edge lies in Driver's axial tree. -/
theorem leftBond_isAxialTree
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeIsAxialTreeBond plaquette.leftBond :=
  Or.inl rfl

end EpsilonSquareLatticePlaquette

namespace epsilonSquareLatticeBoxHorizontalValue

/-- Horizontal-value evaluation is measurable in the finite coordinate configuration. -/
theorem measurable (site : ℤ × ℤ) :
    Measurable (fun configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G =>
      epsilonSquareLatticeBoxHorizontalValue spacing radius configuration site) :=
  (EpsilonSquareLatticeAxialConfiguration.measurable_apply
    (epsilonSquareLatticeRightBond spacing site)).comp
      (epsilonSquareLatticeBoxAxialExtension.measurable spacing radius)

end epsilonSquareLatticeBoxHorizontalValue

omit [MeasurableSpace G] [MeasurableInv G] in
/-- Exact axial plaquette formula under later-traversal-on-the-left path ordering. Vertical edges
are frozen, while the top edge is traversed in reverse, so the upper horizontal value is inverted
and multiplies the lower value on the left. -/
theorem epsilonSquareLatticeBoxAxialPlaquetteHolonomy_eq_horizontalValues
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette
        (epsilonSquareLatticeBoxAxialExtension spacing radius configuration) =
      (epsilonSquareLatticeBoxHorizontalValue spacing radius configuration
        (plaquette.lowerLeft.1, plaquette.lowerLeft.2 + 1))⁻¹ *
      epsilonSquareLatticeBoxHorizontalValue spacing radius configuration
        plaquette.lowerLeft := by
  rw [epsilonSquareLatticeAxialPlaquetteHolonomy,
    epsilonSquareLatticePlaquetteHolonomy]
  rw [(epsilonSquareLatticeBoxAxialExtension spacing radius configuration).axialTree_fixed
      plaquette.leftBond plaquette.leftBond_isAxialTree]
  rw [(epsilonSquareLatticeBoxAxialExtension spacing radius configuration).axialTree_fixed
      plaquette.rightBond plaquette.rightBond_isAxialTree]
  rw [plaquette.topBond_eq_reverse_rightBond,
    (epsilonSquareLatticeBoxAxialExtension spacing radius configuration).configuration.reverse_value]
  rw [plaquette.bottomBond_eq_rightBond]
  simp [epsilonSquareLatticeBoxHorizontalValue]

omit [MeasurableSpace G] [MeasurableInv G] in
/-- The same exact formula on the finite box plaquette subtype. -/
theorem epsilonSquareLatticeBoxAxialPlaquetteHolonomy_eq_horizontalValues_subtype
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
        (epsilonSquareLatticeBoxAxialExtension spacing radius configuration) =
      (epsilonSquareLatticeBoxHorizontalValue spacing radius configuration
        (plaquette.1.lowerLeft.1, plaquette.1.lowerLeft.2 + 1))⁻¹ *
      epsilonSquareLatticeBoxHorizontalValue spacing radius configuration
        plaquette.1.lowerLeft :=
  epsilonSquareLatticeBoxAxialPlaquetteHolonomy_eq_horizontalValues
    spacing radius configuration plaquette.1

/-- The concrete square box as one generic finite axial presentation. -/
def twoDimensionalSquareLatticeBoxPresentation :
    TwoDimensionalFiniteAxialPlaquettePresentationData G spacing where
  Coordinate := EpsilonSquareLatticeBoxCoordinate spacing radius
  coordinateFintype := inferInstance
  coordinateDecidableEq := inferInstance
  coordinateNonempty := by
    let bond := epsilonSquareLatticeRightBond spacing (0, 1)
    have horizontal : (0 : ℤ) ∈ squareLatticeBoxInterval radius :=
      (squareLatticeBoxInterval.mem_iff radius 0).mpr ⟨by omega, by omega⟩
    have row : (1 : ℤ) ∈ squareLatticeBoxOffAxisRows radius :=
      (squareLatticeBoxOffAxisRows.mem_iff radius 1).mpr ⟨by omega, by omega, by norm_num⟩
    exact ⟨⟨bond, epsilonSquareLatticeBoxAxialCoordinates.mem_of_site
      spacing radius (0, 1) horizontal row⟩⟩
  Plaquette := EpsilonSquareLatticeBoxPlaquette spacing radius
  plaquetteFintype := inferInstance
  plaquetteDecidableEq := inferInstance
  plaquetteNonempty := by
    have radiusPositive : (0 : ℤ) < (radius.1 : ℤ) := by exact_mod_cast radius.2
    have membership := (epsilonSquareLatticeBoxPlaquettes.mem_iff spacing radius
      (⟨(0, 0)⟩ : EpsilonSquareLatticePlaquette spacing)).mpr (by
        change (-(radius.1 : ℤ) ≤ 0 ∧ 0 < (radius.1 : ℤ) ∧
          -(radius.1 : ℤ) ≤ 0 ∧ 0 < (radius.1 : ℤ))
        exact ⟨by omega, radiusPositive, by omega, radiusPositive⟩)
    exact ⟨⟨⟨(0, 0)⟩, membership⟩⟩
  coordinateBond := Subtype.val
  coordinateBond_injective := Subtype.val_injective
  coordinateBond_reverse_disjoint := by
    intro first second equality
    have reverseMembership : second.1.reverse ∈
        epsilonSquareLatticeBoxAxialCoordinates spacing radius := by
      rw [← equality]
      exact first.2
    exact (epsilonSquareLatticeBoxAxialCoordinates.reverse_not_mem
      spacing radius second.1 second.2) reverseMembership
  coordinateBond_not_axial := fun coordinate =>
    epsilonSquareLatticeBoxAxialCoordinates.not_axial spacing radius coordinate.1 coordinate.2
  extension := epsilonSquareLatticeBoxAxialExtension spacing radius
  extension_measurable := epsilonSquareLatticeBoxAxialExtension.measurable spacing radius
  extension_coordinate := epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius
  extension_unrepresented := by
    intro configuration bond notTree absent
    apply epsilonSquareLatticeBoxAxialExtension.unrepresented spacing radius configuration bond notTree
    · exact fun membership => (absent ⟨bond, membership⟩).1 rfl
    · exact fun membership => (absent ⟨bond.reverse, membership⟩).2 rfl
  plaquette := Subtype.val
  plaquette_injective := Subtype.val_injective
  plaquette_boundary_covered := by
    intro label bond boundary
    rcases epsilonSquareLatticeBoxAxialCoordinates.plaquette_boundary_covered
      spacing radius label.1 label.2 bond boundary with tree | forward | reverse
    · exact Or.inl tree
    · exact Or.inr ⟨⟨bond, forward⟩, Or.inl rfl⟩
    · exact Or.inr ⟨⟨bond.reverse, reverse⟩, Or.inr rfl⟩

end

end YangMills.Dimensions
