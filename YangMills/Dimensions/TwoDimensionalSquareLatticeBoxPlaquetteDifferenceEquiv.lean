/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxSiteEquiv
import YangMills.Mathematics.RootedGroupDifference

/-!
# Exact plaquette-difference coordinates on square boxes

For each horizontal column, upper and lower off-axis bond values form two rooted finite chains.
Applying the exact upper/lower noncommutative difference equivalences columnwise gives an explicit
measurable equivalence from actual finite box coordinates to actual box plaquette values. The
forward transform is proved pointwise equal to the plaquette holonomy of the same axial extension,
including the source-critical multiplication order.

This constructs finite change-of-coordinate geometry only, not a probability law or projective
limit.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics.RootedGroupDifference

noncomputable section

universe uG

variable {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

/-- Values of one positive-row coordinate chain at a fixed horizontal index. -/
def boxUpperCoordinateChain
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) : Fin radius.1 → G :=
  fun index => configuration
    (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index))

/-- Values of one negative-row coordinate chain at a fixed horizontal index. -/
def boxLowerCoordinateChain
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) : Fin radius.1 → G :=
  fun index => configuration
    (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index))

/-- Plaquette differences on the upper chain at a fixed horizontal index. -/
def boxUpperPlaquetteChain
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) : Fin radius.1 → G :=
  fun index => differences
    (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index))

/-- Plaquette differences on the lower chain at a fixed horizontal index. -/
def boxLowerPlaquetteChain
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) : Fin radius.1 → G :=
  fun index => differences
    (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index))

/-- Exact box coordinate-to-plaquette rooted difference transform. -/
def boxPlaquetteDifferenceForward
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G) :
    EpsilonSquareLatticeBoxPlaquette spacing radius → G :=
  fun plaquette =>
    let chain := (boxPlaquetteChainEquiv spacing radius).symm plaquette
    match chain.2 with
    | Sum.inl index => upperForward (boxUpperCoordinateChain spacing radius configuration chain.1) index
    | Sum.inr index => lowerForward (boxLowerCoordinateChain spacing radius configuration chain.1) index

/-- Explicit recovery from box plaquette differences. -/
def boxPlaquetteDifferenceRecover
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G) :
    EpsilonSquareLatticeBoxCoordinate spacing radius → G :=
  fun coordinate =>
    let chain := (boxCoordinateChainEquiv spacing radius).symm coordinate
    match chain.2 with
    | Sum.inl index => upperRecover (boxUpperPlaquetteChain spacing radius differences chain.1) index
    | Sum.inr index => lowerRecover (boxLowerPlaquetteChain spacing radius differences chain.1) index

@[simp] theorem boxPlaquetteDifferenceForward_chain_inl
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceForward spacing radius configuration
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index)) =
      upperForward (boxUpperCoordinateChain spacing radius configuration horizontal) index := by
  unfold boxPlaquetteDifferenceForward
  rw [Equiv.symm_apply_apply]

@[simp] theorem boxPlaquetteDifferenceForward_chain_inr
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceForward spacing radius configuration
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index)) =
      lowerForward (boxLowerCoordinateChain spacing radius configuration horizontal) index := by
  unfold boxPlaquetteDifferenceForward
  rw [Equiv.symm_apply_apply]

@[simp] theorem boxPlaquetteDifferenceRecover_chain_inl
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceRecover spacing radius differences
        (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index)) =
      upperRecover (boxUpperPlaquetteChain spacing radius differences horizontal) index := by
  unfold boxPlaquetteDifferenceRecover
  rw [Equiv.symm_apply_apply]

@[simp] theorem boxPlaquetteDifferenceRecover_chain_inr
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceRecover spacing radius differences
        (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index)) =
      lowerRecover (boxLowerPlaquetteChain spacing radius differences horizontal) index := by
  unfold boxPlaquetteDifferenceRecover
  rw [Equiv.symm_apply_apply]

/-- Recovery after rooted differences is the identity on actual box coordinates. -/
theorem boxPlaquetteDifferenceRecover_forward
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G) :
    boxPlaquetteDifferenceRecover spacing radius
      (boxPlaquetteDifferenceForward spacing radius configuration) = configuration := by
  funext coordinate
  obtain ⟨⟨horizontal, branch⟩, rfl⟩ :=
    (boxCoordinateChainEquiv spacing radius).surjective coordinate
  rcases branch with index | index
  · rw [boxPlaquetteDifferenceRecover_chain_inl]
    have chain_eq :
        boxUpperPlaquetteChain spacing radius
            (boxPlaquetteDifferenceForward spacing radius configuration) horizontal =
          upperForward (boxUpperCoordinateChain spacing radius configuration horizontal) := by
      funext otherIndex
      exact boxPlaquetteDifferenceForward_chain_inl
        spacing radius configuration horizontal otherIndex
    rw [chain_eq, congrFun (upperRecover_upperForward
      (boxUpperCoordinateChain spacing radius configuration horizontal)) index]
    rfl
  · rw [boxPlaquetteDifferenceRecover_chain_inr]
    have chain_eq :
        boxLowerPlaquetteChain spacing radius
            (boxPlaquetteDifferenceForward spacing radius configuration) horizontal =
          lowerForward (boxLowerCoordinateChain spacing radius configuration horizontal) := by
      funext otherIndex
      exact boxPlaquetteDifferenceForward_chain_inr
        spacing radius configuration horizontal otherIndex
    rw [chain_eq, congrFun (lowerRecover_lowerForward
      (boxLowerCoordinateChain spacing radius configuration horizontal)) index]
    rfl

/-- Rooted differences after recovery are the identity on actual box plaquettes. -/
theorem boxPlaquetteDifferenceForward_recover
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G) :
    boxPlaquetteDifferenceForward spacing radius
      (boxPlaquetteDifferenceRecover spacing radius differences) = differences := by
  funext plaquette
  obtain ⟨⟨horizontal, branch⟩, rfl⟩ :=
    (boxPlaquetteChainEquiv spacing radius).surjective plaquette
  rcases branch with index | index
  · rw [boxPlaquetteDifferenceForward_chain_inl]
    have chain_eq :
        boxUpperCoordinateChain spacing radius
            (boxPlaquetteDifferenceRecover spacing radius differences) horizontal =
          upperRecover (boxUpperPlaquetteChain spacing radius differences horizontal) := by
      funext otherIndex
      exact boxPlaquetteDifferenceRecover_chain_inl
        spacing radius differences horizontal otherIndex
    rw [chain_eq, congrFun (upperForward_upperRecover
      (boxUpperPlaquetteChain spacing radius differences horizontal)) index]
    rfl
  · rw [boxPlaquetteDifferenceForward_chain_inr]
    have chain_eq :
        boxLowerCoordinateChain spacing radius
            (boxPlaquetteDifferenceRecover spacing radius differences) horizontal =
          lowerRecover (boxLowerPlaquetteChain spacing radius differences horizontal) := by
      funext otherIndex
      exact boxPlaquetteDifferenceRecover_chain_inr
        spacing radius differences horizontal otherIndex
    rw [chain_eq, congrFun (lowerForward_lowerRecover
      (boxLowerPlaquetteChain spacing radius differences horizontal)) index]
    rfl

/-- Exact noncommutative equivalence between actual box coordinates and actual box plaquettes. -/
def boxPlaquetteDifferenceEquiv :
    (EpsilonSquareLatticeBoxCoordinate spacing radius → G) ≃
      (EpsilonSquareLatticeBoxPlaquette spacing radius → G) where
  toFun := boxPlaquetteDifferenceForward spacing radius
  invFun := boxPlaquetteDifferenceRecover spacing radius
  left_inv := boxPlaquetteDifferenceRecover_forward spacing radius
  right_inv := boxPlaquetteDifferenceForward_recover spacing radius

@[simp] theorem boxPlaquetteDifferenceEquiv_apply
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G) :
    boxPlaquetteDifferenceEquiv (G := G) spacing radius configuration =
      boxPlaquetteDifferenceForward spacing radius configuration := rfl

@[simp] theorem boxPlaquetteDifferenceEquiv_symm_apply
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G) :
    (boxPlaquetteDifferenceEquiv (G := G) spacing radius).symm differences =
      boxPlaquetteDifferenceRecover spacing radius differences := rfl

/-- The horizontal box value on the axial root row is the identity. -/
@[simp] theorem epsilonSquareLatticeBoxHorizontalValue_axis
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : ℤ) :
    epsilonSquareLatticeBoxHorizontalValue spacing radius configuration (horizontal, 0) = 1 := by
  unfold epsilonSquareLatticeBoxHorizontalValue
  apply (epsilonSquareLatticeBoxAxialExtension spacing radius configuration).axialTree_fixed
  exact Or.inr ⟨rfl, rfl⟩

/-- Positive-chain horizontal values are the exact selected coordinate values. -/
@[simp] theorem epsilonSquareLatticeBoxHorizontalValue_chain_inl
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    epsilonSquareLatticeBoxHorizontalValue spacing radius configuration
        (horizontal.1, (index.1 : ℤ) + 1) =
      boxUpperCoordinateChain spacing radius configuration horizontal index := by
  simpa [epsilonSquareLatticeBoxHorizontalValue, boxUpperCoordinateChain,
    boxCoordinateChainEquiv_apply, boxCoordinateOfSite] using
      epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius configuration
        (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index))

/-- Negative-chain horizontal values are the exact selected coordinate values. -/
@[simp] theorem epsilonSquareLatticeBoxHorizontalValue_chain_inr
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    epsilonSquareLatticeBoxHorizontalValue spacing radius configuration
        (horizontal.1, -((index.1 : ℤ) + 1)) =
      boxLowerCoordinateChain spacing radius configuration horizontal index := by
  simpa [epsilonSquareLatticeBoxHorizontalValue, boxLowerCoordinateChain,
    boxCoordinateChainEquiv_apply, boxCoordinateOfSite] using
      epsilonSquareLatticeBoxAxialExtension.coordinate spacing radius configuration
        (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index))

/-- On every upper-chain plaquette, the rooted forward difference is the exact axial plaquette
holonomy of the same finite box extension. -/
theorem boxPlaquetteDifferenceForward_chain_inl_eq_holonomy
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceForward spacing radius configuration
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index)) =
      epsilonSquareLatticeAxialPlaquetteHolonomy
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index)).1
        (epsilonSquareLatticeBoxAxialExtension spacing radius configuration) := by
  rw [boxPlaquetteDifferenceForward_chain_inl,
    epsilonSquareLatticeBoxAxialPlaquetteHolonomy_eq_horizontalValues_subtype,
    boxPlaquetteChainEquiv_lowerLeft_inl]
  rcases radius with ⟨_ | n, radiusPositive⟩
  · omega
  · refine Fin.cases ?_ (fun previous => ?_) index
    · simpa using (epsilonSquareLatticeBoxHorizontalValue_chain_inl
        spacing ⟨n + 1, radiusPositive⟩ configuration horizontal (0 : Fin (n + 1))).symm
    · rw [upperForward_succ]
      rw [epsilonSquareLatticeBoxHorizontalValue_chain_inl
        spacing ⟨n + 1, radiusPositive⟩ configuration horizontal previous.succ]
      have lowerRow : (previous.succ.1 : ℤ) = (previous.castSucc.1 : ℤ) + 1 := by
        simp
      rw [lowerRow]
      rw [epsilonSquareLatticeBoxHorizontalValue_chain_inl
        spacing ⟨n + 1, radiusPositive⟩ configuration horizontal previous.castSucc]

/-- On every lower-chain plaquette, the rooted forward difference is the exact axial plaquette
holonomy with the unchanged noncommutative multiplication order. -/
theorem boxPlaquetteDifferenceForward_chain_inr_eq_holonomy
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceForward spacing radius configuration
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index)) =
      epsilonSquareLatticeAxialPlaquetteHolonomy
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index)).1
        (epsilonSquareLatticeBoxAxialExtension spacing radius configuration) := by
  rw [boxPlaquetteDifferenceForward_chain_inr,
    epsilonSquareLatticeBoxAxialPlaquetteHolonomy_eq_horizontalValues_subtype,
    boxPlaquetteChainEquiv_lowerLeft_inr]
  rcases radius with ⟨_ | n, radiusPositive⟩
  · omega
  · refine Fin.cases ?_ (fun previous => ?_) index
    · simpa using (epsilonSquareLatticeBoxHorizontalValue_chain_inr
        spacing ⟨n + 1, radiusPositive⟩ configuration horizontal (0 : Fin (n + 1))).symm
    · rw [lowerForward_succ]
      rw [epsilonSquareLatticeBoxHorizontalValue_chain_inr
        spacing ⟨n + 1, radiusPositive⟩ configuration horizontal previous.succ]
      have nextRow : (previous.succ.1 : ℤ) =
          (previous.castSucc.1 : ℤ) + 1 := by simp
      have upperRow : -((previous.succ.1 : ℤ) + 1) + 1 =
          -((previous.castSucc.1 : ℤ) + 1) := by
        rw [nextRow]
        ring
      rw [upperRow]
      rw [epsilonSquareLatticeBoxHorizontalValue_chain_inr
        spacing ⟨n + 1, radiusPositive⟩ configuration horizontal previous.castSucc]

/-- The exact box difference transform is pointwise the actual plaquette-holonomy map of the same
finite extension. -/
theorem boxPlaquetteDifferenceForward_eq_holonomy
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    boxPlaquetteDifferenceForward spacing radius configuration plaquette =
      epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
        (epsilonSquareLatticeBoxAxialExtension spacing radius configuration) := by
  obtain ⟨⟨horizontal, branch⟩, rfl⟩ :=
    (boxPlaquetteChainEquiv spacing radius).surjective plaquette
  rcases branch with index | index
  · exact boxPlaquetteDifferenceForward_chain_inl_eq_holonomy
      spacing radius configuration horizontal index
  · exact boxPlaquetteDifferenceForward_chain_inr_eq_holonomy
      spacing radius configuration horizontal index

section Measurable

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

set_option linter.unusedSectionVars false

private theorem boxUpperCoordinateChain_measurable
    (horizontal : SquareLatticeBoxHorizontalIndex radius) :
    Measurable (fun configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G =>
      boxUpperCoordinateChain spacing radius configuration horizontal) := by
  apply measurable_pi_iff.mpr
  intro index
  exact measurable_pi_apply _

private theorem boxLowerCoordinateChain_measurable
    (horizontal : SquareLatticeBoxHorizontalIndex radius) :
    Measurable (fun configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G =>
      boxLowerCoordinateChain spacing radius configuration horizontal) := by
  apply measurable_pi_iff.mpr
  intro index
  exact measurable_pi_apply _

private theorem boxUpperPlaquetteChain_measurable
    (horizontal : SquareLatticeBoxHorizontalIndex radius) :
    Measurable (fun differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G =>
      boxUpperPlaquetteChain spacing radius differences horizontal) := by
  apply measurable_pi_iff.mpr
  intro index
  exact measurable_pi_apply _

private theorem boxLowerPlaquetteChain_measurable
    (horizontal : SquareLatticeBoxHorizontalIndex radius) :
    Measurable (fun differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G =>
      boxLowerPlaquetteChain spacing radius differences horizontal) := by
  apply measurable_pi_iff.mpr
  intro index
  exact measurable_pi_apply _

/-- The exact forward box difference transform is measurable. -/
theorem boxPlaquetteDifferenceForward_measurable :
    Measurable (boxPlaquetteDifferenceForward (G := G) spacing radius) := by
  apply measurable_pi_iff.mpr
  intro plaquette
  rw [← (boxPlaquetteChainEquiv spacing radius).apply_symm_apply plaquette]
  generalize (boxPlaquetteChainEquiv spacing radius).symm plaquette = chain
  rcases chain with ⟨horizontal, branch⟩
  rcases branch with index | index
  · simpa only [boxPlaquetteDifferenceForward_chain_inl, Function.comp_def] using
      (measurable_pi_apply index).comp
        ((upperForward_measurable (G := G)).comp
          (boxUpperCoordinateChain_measurable spacing radius horizontal))
  · simpa only [boxPlaquetteDifferenceForward_chain_inr, Function.comp_def] using
      (measurable_pi_apply index).comp
        ((lowerForward_measurable (G := G)).comp
          (boxLowerCoordinateChain_measurable spacing radius horizontal))

/-- The exact recursive box recovery transform is measurable. -/
theorem boxPlaquetteDifferenceRecover_measurable :
    Measurable (boxPlaquetteDifferenceRecover (G := G) spacing radius) := by
  apply measurable_pi_iff.mpr
  intro coordinate
  rw [← (boxCoordinateChainEquiv spacing radius).apply_symm_apply coordinate]
  generalize (boxCoordinateChainEquiv spacing radius).symm coordinate = chain
  rcases chain with ⟨horizontal, branch⟩
  rcases branch with index | index
  · simpa only [boxPlaquetteDifferenceRecover_chain_inl, Function.comp_def] using
      (measurable_pi_apply index).comp
        ((upperRecover_measurable (G := G)).comp
          (boxUpperPlaquetteChain_measurable spacing radius horizontal))
  · simpa only [boxPlaquetteDifferenceRecover_chain_inr, Function.comp_def] using
      (measurable_pi_apply index).comp
        ((lowerRecover_measurable (G := G)).comp
          (boxLowerPlaquetteChain_measurable spacing radius horizontal))

/-- Exact box differences as a measurable equivalence. -/
def boxPlaquetteDifferenceMeasurableEquiv :
    (EpsilonSquareLatticeBoxCoordinate spacing radius → G) ≃ᵐ
      (EpsilonSquareLatticeBoxPlaquette spacing radius → G) :=
  MeasurableEquiv.mk (boxPlaquetteDifferenceEquiv (G := G) spacing radius)
    (boxPlaquetteDifferenceForward_measurable spacing radius)
    (boxPlaquetteDifferenceRecover_measurable spacing radius)

end Measurable

end

end YangMills.Dimensions
