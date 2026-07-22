/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveSequence

/-!
# Exact infinite axial recovery from plaquette variables

Arbitrary group values on all elementary plaquettes determine one axial configuration: horizontal
values are finite noncommutative rooted products away from the identity row, reverse bonds are
inverted, and the axial tree is fixed to one. The recovery map is measurable, recovers every input
plaquette holonomy exactly, and restricts on each finite box to the existing recursive box recovery.

No probability measure or convergence statement is constructed in this file.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics
open YangMills.Mathematics.RootedGroupDifference

noncomputable section

universe uG

variable {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing)

/-- Recursive positive-row axial recovery from plaquette values. -/
def infiniteAxialUpperHorizontalRecover
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) (horizontal : ℤ) : ℕ → G
  | 0 => 1
  | n + 1 => infiniteAxialUpperHorizontalRecover plaquettes horizontal n *
      (plaquettes ⟨(horizontal, (n : ℤ))⟩)⁻¹

/-- Recursive negative-row axial recovery from plaquette values. -/
def infiniteAxialLowerHorizontalRecover
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) (horizontal : ℤ) : ℕ → G
  | 0 => 1
  | n + 1 => infiniteAxialLowerHorizontalRecover plaquettes horizontal n *
      plaquettes ⟨(horizontal, -((n : ℤ) + 1))⟩

/-- Axial horizontal value at an arbitrary integer site, rooted at identity on row zero. -/
def infiniteAxialHorizontalRecover
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) (site : ℤ × ℤ) : G :=
  if _positive : 0 < site.2 then
    infiniteAxialUpperHorizontalRecover spacing plaquettes site.1 site.2.toNat
  else if _negative : site.2 < 0 then
    infiniteAxialLowerHorizontalRecover spacing plaquettes site.1 (-site.2).toNat
  else 1

/-- Recovered value on an arbitrary directed nearest-neighbor bond. Right-directed horizontal bonds
use the rooted value at their source, left-directed bonds use its inverse at their target, and all
vertical bonds are one. -/
def infiniteAxialRecoveredBondValue
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing) : G :=
  if _right : bond.target.1 = bond.source.1 + 1 then
    infiniteAxialHorizontalRecover spacing plaquettes bond.source
  else if _left : bond.source.1 = bond.target.1 + 1 then
    (infiniteAxialHorizontalRecover spacing plaquettes bond.target)⁻¹
  else 1

private theorem infiniteAxialHorizontalRecover_of_row_zero
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) (site : ℤ × ℤ)
    (rowZero : site.2 = 0) :
    infiniteAxialHorizontalRecover spacing plaquettes site = 1 := by
  simp [infiniteAxialHorizontalRecover, rowZero]

private theorem infiniteAxialRecoveredBondValue_reverse
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    infiniteAxialRecoveredBondValue spacing plaquettes bond.reverse =
      (infiniteAxialRecoveredBondValue spacing plaquettes bond)⁻¹ := by
  unfold infiniteAxialRecoveredBondValue
  simp only [EpsilonSquareLatticeDirectedBond.reverse_source,
    EpsilonSquareLatticeDirectedBond.reverse_target]
  by_cases right : bond.target.1 = bond.source.1 + 1
  · have notLeft : bond.source.1 ≠ bond.target.1 + 1 := by omega
    rw [dif_neg notLeft, dif_pos right, dif_pos right]
  · by_cases left : bond.source.1 = bond.target.1 + 1
    · rw [dif_pos left, dif_neg right, dif_pos left]
      simp
    · rw [dif_neg left, dif_neg right, dif_neg right, dif_neg left]
      simp

private theorem infiniteAxialRecoveredBondValue_tree
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (tree : epsilonSquareLatticeIsAxialTreeBond bond) :
    infiniteAxialRecoveredBondValue spacing plaquettes bond = 1 := by
  rcases tree with vertical | axis
  · have notRight : bond.target.1 ≠ bond.source.1 + 1 := by omega
    have notLeft : bond.source.1 ≠ bond.target.1 + 1 := by omega
    unfold infiniteAxialRecoveredBondValue
    rw [dif_neg notRight, dif_neg notLeft]
  · rcases axis with ⟨sourceAxis, targetAxis⟩
    by_cases right : bond.target.1 = bond.source.1 + 1
    · unfold infiniteAxialRecoveredBondValue
      rw [dif_pos right,
        infiniteAxialHorizontalRecover_of_row_zero spacing plaquettes bond.source sourceAxis]
    · by_cases left : bond.source.1 = bond.target.1 + 1
      · unfold infiniteAxialRecoveredBondValue
        rw [dif_neg right, dif_pos left,
          infiniteAxialHorizontalRecover_of_row_zero spacing plaquettes bond.target targetAxis]
        simp
      · unfold infiniteAxialRecoveredBondValue
        rw [dif_neg right, dif_neg left]

/-- Exact infinite axial recovery from arbitrary plaquette values. -/
def infiniteAxialRecover
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) :
    EpsilonSquareLatticeAxialConfiguration G spacing where
  configuration :=
    { value := infiniteAxialRecoveredBondValue spacing plaquettes
      reverse_value := infiniteAxialRecoveredBondValue_reverse spacing plaquettes }
  axialTree_fixed := infiniteAxialRecoveredBondValue_tree spacing plaquettes

section Measurable

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

private theorem infiniteAxialUpperHorizontalRecover_measurable
    (horizontal : ℤ) : ∀ n : ℕ,
    Measurable (fun plaquettes : EpsilonSquareLatticePlaquette spacing → G =>
      infiniteAxialUpperHorizontalRecover spacing plaquettes horizontal n)
  | 0 => by simp [infiniteAxialUpperHorizontalRecover]
  | n + 1 => by
      simpa only [infiniteAxialUpperHorizontalRecover] using
        (infiniteAxialUpperHorizontalRecover_measurable horizontal n).mul
          (measurable_pi_apply (⟨(horizontal, (n : ℤ))⟩ :
            EpsilonSquareLatticePlaquette spacing)).inv

omit [MeasurableInv G] in
private theorem infiniteAxialLowerHorizontalRecover_measurable
    (horizontal : ℤ) : ∀ n : ℕ,
    Measurable (fun plaquettes : EpsilonSquareLatticePlaquette spacing → G =>
      infiniteAxialLowerHorizontalRecover spacing plaquettes horizontal n)
  | 0 => by simp [infiniteAxialLowerHorizontalRecover]
  | n + 1 => by
      simpa only [infiniteAxialLowerHorizontalRecover] using
        (infiniteAxialLowerHorizontalRecover_measurable horizontal n).mul
          (measurable_pi_apply (⟨(horizontal, -((n : ℤ) + 1))⟩ :
            EpsilonSquareLatticePlaquette spacing))

private theorem infiniteAxialHorizontalRecover_measurable (site : ℤ × ℤ) :
    Measurable (fun plaquettes : EpsilonSquareLatticePlaquette spacing → G =>
      infiniteAxialHorizontalRecover spacing plaquettes site) := by
  by_cases positive : 0 < site.2
  · simpa [infiniteAxialHorizontalRecover, positive] using
      infiniteAxialUpperHorizontalRecover_measurable (spacing := spacing) site.1 site.2.toNat
  · by_cases negative : site.2 < 0
    · simpa [infiniteAxialHorizontalRecover, positive, negative] using
        infiniteAxialLowerHorizontalRecover_measurable (spacing := spacing) site.1 (-site.2).toNat
    · simp [infiniteAxialHorizontalRecover, positive, negative]

private theorem infiniteAxialRecoveredBondValue_measurable
    (bond : EpsilonSquareLatticeDirectedBond spacing) :
    Measurable (fun plaquettes : EpsilonSquareLatticePlaquette spacing → G =>
      infiniteAxialRecoveredBondValue spacing plaquettes bond) := by
  by_cases right : bond.target.1 = bond.source.1 + 1
  · simpa [infiniteAxialRecoveredBondValue, right] using
      infiniteAxialHorizontalRecover_measurable (spacing := spacing) bond.source
  · by_cases left : bond.source.1 = bond.target.1 + 1
    · have inverseMeasurable : Measurable
          (fun plaquettes : EpsilonSquareLatticePlaquette spacing → G =>
            (infiniteAxialHorizontalRecover spacing plaquettes bond.target)⁻¹) :=
        (infiniteAxialHorizontalRecover_measurable (spacing := spacing) bond.target).inv
      have functionEquality :
          (fun plaquettes : EpsilonSquareLatticePlaquette spacing → G =>
            infiniteAxialRecoveredBondValue spacing plaquettes bond) =
          (fun plaquettes =>
            (infiniteAxialHorizontalRecover spacing plaquettes bond.target)⁻¹) := by
        funext plaquettes
        unfold infiniteAxialRecoveredBondValue
        rw [dif_neg right, dif_pos left]
      rw [functionEquality]
      exact inverseMeasurable
    · simp [infiniteAxialRecoveredBondValue, right, left]

/-- Infinite axial recovery is measurable for the induced configuration sigma field. -/
theorem infiniteAxialRecover_measurable :
    Measurable (infiniteAxialRecover (G := G) spacing) := by
  apply (measurable_comap_iff
    (g := EpsilonSquareLatticeAxialConfiguration.configuration)).mpr
  apply (measurable_comap_iff
    (g := EpsilonSquareLatticeConfiguration.value)).mpr
  apply measurable_pi_iff.mpr
  exact infiniteAxialRecoveredBondValue_measurable (spacing := spacing)

end Measurable


/-- Restr global plaquette values to one exact finite box. -/
def infinitePlaquetteBoxRestriction
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) :
    EpsilonSquareLatticeBoxPlaquette spacing radius → G :=
  fun plaquette => plaquettes plaquette.1

section FiniteCoherence

omit [Group G] in
@[simp] private theorem infinitePlaquetteBoxRestriction_upper_chain
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxUpperPlaquetteChain spacing radius
        (infinitePlaquetteBoxRestriction spacing radius plaquettes) horizontal index =
      plaquettes ⟨(horizontal.1, (index.1 : ℤ))⟩ := by
  unfold boxUpperPlaquetteChain infinitePlaquetteBoxRestriction
  congr 1

omit [Group G] in
@[simp] private theorem infinitePlaquetteBoxRestriction_lower_chain
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxLowerPlaquetteChain spacing radius
        (infinitePlaquetteBoxRestriction spacing radius plaquettes) horizontal index =
      plaquettes ⟨(horizontal.1, -((index.1 : ℤ) + 1))⟩ := by
  unfold boxLowerPlaquetteChain infinitePlaquetteBoxRestriction
  congr 1

private theorem infiniteAxialUpperHorizontalRecover_eq_upperRecover
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    infiniteAxialUpperHorizontalRecover spacing plaquettes horizontal.1 (index.1 + 1) =
      upperRecover
        (boxUpperPlaquetteChain spacing radius
          (infinitePlaquetteBoxRestriction spacing radius plaquettes) horizontal) index := by
  rcases radius with ⟨_ | n, radiusPositive⟩
  · omega
  · induction index using Fin.induction with
    | zero =>
        simp [infiniteAxialUpperHorizontalRecover]
    | succ index ih =>
        rw [upperRecover_succ]
        rw [show index.succ.1 + 1 = (index.castSucc.1 + 1) + 1 by simp]
        rw [infiniteAxialUpperHorizontalRecover, ih]
        congr 1

private theorem infiniteAxialLowerHorizontalRecover_eq_lowerRecover
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    infiniteAxialLowerHorizontalRecover spacing plaquettes horizontal.1 (index.1 + 1) =
      lowerRecover
        (boxLowerPlaquetteChain spacing radius
          (infinitePlaquetteBoxRestriction spacing radius plaquettes) horizontal) index := by
  rcases radius with ⟨_ | n, radiusPositive⟩
  · omega
  · induction index using Fin.induction with
    | zero =>
        simp [infiniteAxialLowerHorizontalRecover]
    | succ index ih =>
        rw [lowerRecover_succ]
        rw [show index.succ.1 + 1 = (index.castSucc.1 + 1) + 1 by simp]
        rw [infiniteAxialLowerHorizontalRecover, ih]
        congr 1

private theorem infiniteAxialHorizontalRecover_chain_inl
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    infiniteAxialHorizontalRecover spacing plaquettes
        (horizontal.1, (index.1 : ℤ) + 1) =
      upperRecover
        (boxUpperPlaquetteChain spacing radius
          (infinitePlaquetteBoxRestriction spacing radius plaquettes) horizontal) index := by
  have positive : (0 : ℤ) < (index.1 : ℤ) + 1 := by omega
  have toNatEq : ((index.1 : ℤ) + 1).toNat = index.1 + 1 := by omega
  rw [infiniteAxialHorizontalRecover, dif_pos positive, toNatEq]
  exact infiniteAxialUpperHorizontalRecover_eq_upperRecover
    spacing radius plaquettes horizontal index

private theorem infiniteAxialHorizontalRecover_chain_inr
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    infiniteAxialHorizontalRecover spacing plaquettes
        (horizontal.1, -((index.1 : ℤ) + 1)) =
      lowerRecover
        (boxLowerPlaquetteChain spacing radius
          (infinitePlaquetteBoxRestriction spacing radius plaquettes) horizontal) index := by
  have notPositive : ¬ (0 : ℤ) < -((index.1 : ℤ) + 1) := by omega
  have negative : -((index.1 : ℤ) + 1) < (0 : ℤ) := by omega
  have toNatEq : (-(-((index.1 : ℤ) + 1))).toNat = index.1 + 1 := by omega
  rw [infiniteAxialHorizontalRecover, dif_neg notPositive, dif_pos negative, toNatEq]
  exact infiniteAxialLowerHorizontalRecover_eq_lowerRecover
    spacing radius plaquettes horizontal index

/-- Restring global recovered axial coordinates to any exact box equals finite rooted recovery from
that box's literal plaquette restriction. -/
theorem infiniteAxialRecover_boxCoordinateRestriction
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G) :
    (fun coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius =>
      infiniteAxialRecover spacing plaquettes coordinate.1) =
      boxPlaquetteDifferenceRecover spacing radius
        (infinitePlaquetteBoxRestriction spacing radius plaquettes) := by
  funext coordinate
  obtain ⟨⟨horizontal, branch⟩, rfl⟩ :=
    (boxCoordinateChainEquiv spacing radius).surjective coordinate
  rcases branch with index | index
  · rw [boxPlaquetteDifferenceRecover_chain_inl]
    change infiniteAxialRecoveredBondValue spacing plaquettes
      (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index)).1 = _
    unfold infiniteAxialRecoveredBondValue
    have right :
        (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index)).1.target.1 =
          (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index)).1.source.1 + 1 := by
      rfl
    rw [dif_pos right]
    rw [boxCoordinateChainEquiv_source_inl]
    exact infiniteAxialHorizontalRecover_chain_inl
      spacing radius plaquettes horizontal index
  · rw [boxPlaquetteDifferenceRecover_chain_inr]
    change infiniteAxialRecoveredBondValue spacing plaquettes
      (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index)).1 = _
    unfold infiniteAxialRecoveredBondValue
    have right :
        (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index)).1.target.1 =
          (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index)).1.source.1 + 1 := by
      rfl
    rw [dif_pos right]
    rw [boxCoordinateChainEquiv_source_inr]
    exact infiniteAxialHorizontalRecover_chain_inr
      spacing radius plaquettes horizontal index


/-- The finite extension of global recovered coordinates agrees with global recovery on every bond
of every selected finite-box plaquette boundary. -/
theorem infiniteAxialRecover_finiteExtension_on_plaquetteBoundary
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius)
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (boundaryMembership : bond ∈ plaquette.1.boundaryBonds) :
    epsilonSquareLatticeBoxAxialExtension spacing radius
        (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1) bond =
      infiniteAxialRecover spacing plaquettes bond := by
  rcases epsilonSquareLatticeBoxAxialCoordinates.plaquette_boundary_covered
    spacing radius plaquette.1 plaquette.2 bond boundaryMembership with
      tree | forward | reverse
  · rw [(epsilonSquareLatticeBoxAxialExtension spacing radius
      (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1)).axialTree_fixed
        bond tree]
    rw [(infiniteAxialRecover spacing plaquettes).axialTree_fixed bond tree]
  · let coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius := ⟨bond, forward⟩
    simpa [coordinate] using
      epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius
        (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1) coordinate
  · let coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius := ⟨bond.reverse, reverse⟩
    have finiteReverse :
        epsilonSquareLatticeBoxAxialExtension spacing radius
            (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1) bond =
          (epsilonSquareLatticeBoxAxialExtension spacing radius
            (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1)
              bond.reverse)⁻¹ := by
      simpa using (epsilonSquareLatticeBoxAxialExtension spacing radius
        (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1)).configuration.reverse_value
          bond.reverse
    have globalReverse :
        infiniteAxialRecover spacing plaquettes bond =
          (infiniteAxialRecover spacing plaquettes bond.reverse)⁻¹ := by
      simpa using (infiniteAxialRecover spacing plaquettes).configuration.reverse_value bond.reverse
    rw [finiteReverse, globalReverse]
    congr 1
    simpa [coordinate] using
      epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius
        (fun coordinate => infiniteAxialRecover spacing plaquettes coordinate.1) coordinate

/-- Every selected finite-box plaquette recovers exactly its original global plaquette variable. -/
theorem infiniteAxialRecover_boxPlaquetteHolonomy
    (radius : PositiveSquareLatticeBoxRadius)
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
        (infiniteAxialRecover spacing plaquettes) = plaquettes plaquette.1 := by
  let finiteValues := infinitePlaquetteBoxRestriction spacing radius plaquettes
  let finiteCoordinates := boxPlaquetteDifferenceRecover spacing radius finiteValues
  have coordinateEquality :
      (fun coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius =>
        infiniteAxialRecover spacing plaquettes coordinate.1) = finiteCoordinates :=
    infiniteAxialRecover_boxCoordinateRestriction spacing radius plaquettes
  have finiteHolonomy :
      epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
        (epsilonSquareLatticeBoxAxialExtension spacing radius finiteCoordinates) =
        finiteValues plaquette := by
    rw [← boxPlaquetteDifferenceForward_eq_holonomy]
    exact congrFun (boxPlaquetteDifferenceForward_recover spacing radius finiteValues) plaquette
  change epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
      (infiniteAxialRecover spacing plaquettes) = finiteValues plaquette
  rw [← finiteHolonomy]
  unfold epsilonSquareLatticeAxialPlaquetteHolonomy epsilonSquareLatticePlaquetteHolonomy
  rw [← coordinateEquality]
  rw [infiniteAxialRecover_finiteExtension_on_plaquetteBoundary
      spacing radius plaquettes plaquette plaquette.1.leftBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]
  rw [infiniteAxialRecover_finiteExtension_on_plaquetteBoundary
      spacing radius plaquettes plaquette plaquette.1.topBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]
  rw [infiniteAxialRecover_finiteExtension_on_plaquetteBoundary
      spacing radius plaquettes plaquette plaquette.1.rightBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]
  rw [infiniteAxialRecover_finiteExtension_on_plaquetteBoundary
      spacing radius plaquettes plaquette plaquette.1.bottomBond (by simp
        [EpsilonSquareLatticePlaquette.boundaryBonds])]

/-- Global recovery is a right inverse to the exact plaquette-holonomy map at every elementary
plaquette. -/
theorem infiniteAxialRecover_plaquetteHolonomy
    (plaquettes : EpsilonSquareLatticePlaquette spacing → G)
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    epsilonSquareLatticeAxialPlaquetteHolonomy plaquette
        (infiniteAxialRecover spacing plaquettes) = plaquettes plaquette := by
  obtain ⟨stage, label, equality⟩ :=
    squareLatticeBoxProjectiveRadius_plaquette_eventually_selected plaquette
  rw [← equality]
  exact infiniteAxialRecover_boxPlaquetteHolonomy spacing
    (squareLatticeBoxProjectiveRadius stage) plaquettes label

section MeasurableCoherence

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Literal restriction from global plaquette values to any finite box is measurable. -/
theorem infinitePlaquetteBoxRestriction_measurable
    (radius : PositiveSquareLatticeBoxRadius) :
    Measurable (infinitePlaquetteBoxRestriction (G := G) spacing radius) := by
  apply measurable_pi_iff.mpr
  intro plaquette
  exact measurable_pi_apply plaquette.1

end MeasurableCoherence

end FiniteCoherence


end

end YangMills.Dimensions
