/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectivityDerived
import YangMills.Dimensions.TwoDimensionalAxialInfiniteVolumeCylinderLaw

/-!
# Exhaustive projective sequence of exact square boxes

The recursively chosen radii `stage + 1` make consecutive inclusions definitionally exact. Every
off-tree directed bond occurs eventually in one orientation and every elementary plaquette occurs
eventually. Combining this cofinal geometry with derived box projectivity constructs the existing
finite axial projective-sequence contract for every normalized Definition 7.1 action.

This constructs no infinite-volume cylinder measure or convergence theorem.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

universe uG

/-- Positive radius `stage + 1`, defined recursively so successor inclusions are definitionally exact. -/
def squareLatticeBoxProjectiveRadius : ℕ → PositiveSquareLatticeBoxRadius
  | 0 => ⟨1, by omega⟩
  | stage + 1 => squareLatticeBoxSuccessorRadius (squareLatticeBoxProjectiveRadius stage)

@[simp]
theorem squareLatticeBoxProjectiveRadius_zero :
    squareLatticeBoxProjectiveRadius 0 = (⟨1, by omega⟩ : PositiveSquareLatticeBoxRadius) :=
  rfl

@[simp]
theorem squareLatticeBoxProjectiveRadius_succ (stage : ℕ) :
    squareLatticeBoxProjectiveRadius (stage + 1) =
      squareLatticeBoxSuccessorRadius (squareLatticeBoxProjectiveRadius stage) :=
  rfl

@[simp]
theorem squareLatticeBoxProjectiveRadius_value (stage : ℕ) :
    (squareLatticeBoxProjectiveRadius stage).1 = stage + 1 := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      rw [squareLatticeBoxProjectiveRadius_succ,
        squareLatticeBoxSuccessorRadius_value, ih]

private theorem neg_natAbs_le (value : ℤ) :
    -((value.natAbs : ℕ) : ℤ) ≤ value := by
  have bound := Int.le_natAbs (a := -value)
  rw [Int.natAbs_neg] at bound
  omega

private theorem coordinate_bounds_at_cover_stage (horizontal row : ℤ) :
    horizontal ∈ squareLatticeBoxInterval
        (squareLatticeBoxProjectiveRadius (max horizontal.natAbs row.natAbs)) ∧
      row ∈ squareLatticeBoxOffAxisRows
        (squareLatticeBoxProjectiveRadius (max horizontal.natAbs row.natAbs)) ↔
      row ≠ 0 := by
  let stage := max horizontal.natAbs row.natAbs
  have horizontalUpper := Int.le_natAbs (a := horizontal)
  have horizontalLower := neg_natAbs_le horizontal
  have rowUpper := Int.le_natAbs (a := row)
  have rowLower := neg_natAbs_le row
  have horizontalAbsLe : horizontal.natAbs ≤ stage := Nat.le_max_left _ _
  have rowAbsLe : row.natAbs ≤ stage := Nat.le_max_right _ _
  have radiusValue : (squareLatticeBoxProjectiveRadius stage).1 = stage + 1 :=
    squareLatticeBoxProjectiveRadius_value stage
  constructor
  · intro membership
    exact membership.2 |> (squareLatticeBoxOffAxisRows.mem_iff _ _).mp |>.2.2
  · intro rowNonzero
    constructor
    · apply (squareLatticeBoxInterval.mem_iff _ _).mpr
      rw [radiusValue]
      constructor <;> omega
    · apply (squareLatticeBoxOffAxisRows.mem_iff _ _).mpr
      rw [radiusValue]
      constructor
      · omega
      constructor <;> omega

/-- Every off-tree directed nearest-neighbor bond occurs in a projective-radius box in one of the
exact two orientations. -/
theorem squareLatticeBoxProjectiveRadius_bond_eventually_represented
    {spacing : PositiveLatticeSpacing}
    (bond : EpsilonSquareLatticeDirectedBond spacing)
    (notTree : ¬ epsilonSquareLatticeIsAxialTreeBond bond) :
    ∃ stage, ∃ coordinate : EpsilonSquareLatticeBoxCoordinate spacing
        (squareLatticeBoxProjectiveRadius stage),
      bond = coordinate.1 ∨ bond = coordinate.1.reverse := by
  rcases bond.nearestNeighbor with horizontal | vertical
  · rcases horizontal with ⟨right | left, sameRow⟩
    · let stage := max bond.source.1.natAbs bond.source.2.natAbs
      have rowNonzero : bond.source.2 ≠ 0 := by
        intro rowZero
        apply notTree
        exact Or.inr ⟨rowZero, sameRow ▸ rowZero⟩
      have bounds := (coordinate_bounds_at_cover_stage bond.source.1 bond.source.2).mpr rowNonzero
      have membership := epsilonSquareLatticeBoxAxialCoordinates.mem_of_site spacing
        (squareLatticeBoxProjectiveRadius stage) bond.source bounds.1 bounds.2
      have bondEquality : bond = epsilonSquareLatticeRightBond spacing bond.source := by
        apply EpsilonSquareLatticeDirectedBond.ext
        · rfl
        · apply Prod.ext
          · exact right
          · exact sameRow
      exact ⟨stage, ⟨epsilonSquareLatticeRightBond spacing bond.source, membership⟩,
        Or.inl bondEquality⟩
    · let stage := max bond.target.1.natAbs bond.target.2.natAbs
      have rowNonzero : bond.target.2 ≠ 0 := by
        intro rowZero
        apply notTree
        exact Or.inr ⟨sameRow.symm.trans rowZero, rowZero⟩
      have bounds := (coordinate_bounds_at_cover_stage bond.target.1 bond.target.2).mpr rowNonzero
      have membership := epsilonSquareLatticeBoxAxialCoordinates.mem_of_site spacing
        (squareLatticeBoxProjectiveRadius stage) bond.target bounds.1 bounds.2
      have bondEquality : bond =
          (epsilonSquareLatticeRightBond spacing bond.target).reverse := by
        apply EpsilonSquareLatticeDirectedBond.ext
        · apply Prod.ext
          · simp [epsilonSquareLatticeRightBond]
            omega
          · exact sameRow.symm
        · rfl
      exact ⟨stage, ⟨epsilonSquareLatticeRightBond spacing bond.target, membership⟩,
        Or.inr bondEquality⟩
  · apply False.elim
    apply notTree
    exact Or.inl vertical.2.symm

/-- Every elementary plaquette occurs at some projective radius. -/
theorem squareLatticeBoxProjectiveRadius_plaquette_eventually_selected
    {spacing : PositiveLatticeSpacing}
    (plaquette : EpsilonSquareLatticePlaquette spacing) :
    ∃ stage, ∃ label : EpsilonSquareLatticeBoxPlaquette spacing
        (squareLatticeBoxProjectiveRadius stage),
      label.1 = plaquette := by
  let stage := max plaquette.lowerLeft.1.natAbs plaquette.lowerLeft.2.natAbs
  have horizontalUpper := Int.le_natAbs (a := plaquette.lowerLeft.1)
  have horizontalLower := neg_natAbs_le plaquette.lowerLeft.1
  have rowUpper := Int.le_natAbs (a := plaquette.lowerLeft.2)
  have rowLower := neg_natAbs_le plaquette.lowerLeft.2
  have horizontalAbsLe : plaquette.lowerLeft.1.natAbs ≤ stage := Nat.le_max_left _ _
  have rowAbsLe : plaquette.lowerLeft.2.natAbs ≤ stage := Nat.le_max_right _ _
  have radiusValue : (squareLatticeBoxProjectiveRadius stage).1 = stage + 1 :=
    squareLatticeBoxProjectiveRadius_value stage
  have horizontalMembership : plaquette.lowerLeft.1 ∈
      squareLatticeBoxInterval (squareLatticeBoxProjectiveRadius stage) := by
    apply (squareLatticeBoxInterval.mem_iff _ _).mpr
    rw [radiusValue]
    constructor <;> omega
  have rowMembership : plaquette.lowerLeft.2 ∈
      squareLatticeBoxInterval (squareLatticeBoxProjectiveRadius stage) := by
    apply (squareLatticeBoxInterval.mem_iff _ _).mpr
    rw [radiusValue]
    constructor <;> omega
  have membership : plaquette ∈ epsilonSquareLatticeBoxPlaquettes spacing
      (squareLatticeBoxProjectiveRadius stage) := by
    rw [epsilonSquareLatticeBoxPlaquettes]
    apply Finset.mem_image.mpr
    exact ⟨plaquette.lowerLeft,
      Finset.mem_product.mpr ⟨horizontalMembership, rowMembership⟩, by cases plaquette; rfl⟩
  exact ⟨stage, ⟨plaquette, membership⟩, rfl⟩

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (action : TwoDimensionalLatticeActionData G)

/-- Exact exhaustive square-box projective sequence for every normalized Definition 7.1 action. -/
def twoDimensionalSquareLatticeBoxProjectiveSequenceData :
    TwoDimensionalFiniteAxialProjectiveSequenceData (spacing := spacing) action where
  presentation stage := twoDimensionalSquareLatticeBoxPresentation spacing
    (squareLatticeBoxProjectiveRadius stage)
  normalizer stage := twoDimensionalSquareLatticeBoxNormalizerData spacing
    (squareLatticeBoxProjectiveRadius stage) action
  coordinateInclusion stage := epsilonSquareLatticeBoxCoordinateInclusion spacing
    (squareLatticeBoxProjectiveRadius stage)
  coordinateInclusion_injective stage :=
    epsilonSquareLatticeBoxCoordinateInclusion.injective spacing
      (squareLatticeBoxProjectiveRadius stage)
  coordinateBond_inclusion stage coordinate := by
    rfl
  plaquetteInclusion stage := epsilonSquareLatticeBoxPlaquetteInclusion spacing
    (squareLatticeBoxProjectiveRadius stage)
  plaquetteInclusion_injective stage :=
    epsilonSquareLatticeBoxPlaquetteInclusion.injective spacing
      (squareLatticeBoxProjectiveRadius stage)
  plaquette_inclusion stage label := by
    rfl
  bond_eventually_represented bond notTree :=
    squareLatticeBoxProjectiveRadius_bond_eventually_represented bond notTree
  plaquette_eventually_selected plaquette :=
    squareLatticeBoxProjectiveRadius_plaquette_eventually_selected plaquette
  finiteMeasure_projective stage := by
    exact twoDimensionalSquareLatticeBoxMeasure_consecutive_pushforward spacing
      (squareLatticeBoxProjectiveRadius stage) action

end

end YangMills.Dimensions
