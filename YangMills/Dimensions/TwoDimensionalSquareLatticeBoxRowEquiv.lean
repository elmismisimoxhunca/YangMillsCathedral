/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBox

/-!
# Exact chain enumerations of square-box rows

The nonzero horizontal-coordinate rows and plaquette lower-left rows of a positive-radius square
box each split into two exact chains of length `radius`: positive/upward and negative/downward.
These explicit equivalences retain the integer row formulas needed by the noncommutative rooted
difference transform; an arbitrary finite-cardinality equivalence would not suffice.

This file constructs finite row geometry only, not a measure or projective limit.
-/

namespace YangMills.Dimensions

noncomputable section

/-- Off-axis horizontal rows in one exact positive-radius box. -/
abbrev SquareLatticeBoxOffAxisRow (radius : PositiveSquareLatticeBoxRadius) :=
  {row : ℤ // row ∈ squareLatticeBoxOffAxisRows radius}

/-- Plaquette lower-left rows in one exact positive-radius box. -/
abbrev SquareLatticeBoxPlaquetteRow (radius : PositiveSquareLatticeBoxRadius) :=
  {row : ℤ // row ∈ squareLatticeBoxInterval radius}

/-- Explicit positive/negative-chain enumeration of all off-axis horizontal rows. -/
def boxOffAxisRowOfSum (radius : PositiveSquareLatticeBoxRadius) :
    Fin radius.1 ⊕ Fin radius.1 → SquareLatticeBoxOffAxisRow radius
  | Sum.inl index =>
      ⟨(index.1 : ℤ) + 1,
        (squareLatticeBoxOffAxisRows.mem_iff radius _).mpr (by
          have index_lt : (index.1 : ℤ) < (radius.1 : ℤ) := by exact_mod_cast index.2
          constructor
          · omega
          constructor <;> omega)⟩
  | Sum.inr index =>
      ⟨-((index.1 : ℤ) + 1),
        (squareLatticeBoxOffAxisRows.mem_iff radius _).mpr (by
          have index_lt : (index.1 : ℤ) < (radius.1 : ℤ) := by exact_mod_cast index.2
          constructor
          · omega
          constructor <;> omega)⟩

@[simp]
theorem boxOffAxisRowOfSum_inl (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowOfSum radius (Sum.inl index)).1 = (index.1 : ℤ) + 1 :=
  rfl

@[simp]
theorem boxOffAxisRowOfSum_inr (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowOfSum radius (Sum.inr index)).1 = -((index.1 : ℤ) + 1) :=
  rfl

private theorem boxOffAxisRowOfSum_injective (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (boxOffAxisRowOfSum radius) := by
  intro first second equality
  rcases first with first | first <;> rcases second with second | second
  · apply congrArg Sum.inl
    apply Fin.ext
    have values := congrArg Subtype.val equality
    simp only [boxOffAxisRowOfSum_inl] at values
    exact_mod_cast (show (first.1 : ℤ) = second.1 by omega)
  · have values := congrArg Subtype.val equality
    simp only [boxOffAxisRowOfSum_inl, boxOffAxisRowOfSum_inr] at values
    have first_nonneg : (0 : ℤ) ≤ first.1 := by exact_mod_cast Nat.zero_le first.1
    have second_nonneg : (0 : ℤ) ≤ second.1 := by exact_mod_cast Nat.zero_le second.1
    omega
  · have values := congrArg Subtype.val equality
    simp only [boxOffAxisRowOfSum_inr, boxOffAxisRowOfSum_inl] at values
    have first_nonneg : (0 : ℤ) ≤ first.1 := by exact_mod_cast Nat.zero_le first.1
    have second_nonneg : (0 : ℤ) ≤ second.1 := by exact_mod_cast Nat.zero_le second.1
    omega
  · apply congrArg Sum.inr
    apply Fin.ext
    have values := congrArg Subtype.val equality
    simp only [boxOffAxisRowOfSum_inr] at values
    exact_mod_cast (show (first.1 : ℤ) = second.1 by omega)

private theorem boxOffAxisRowOfSum_surjective (radius : PositiveSquareLatticeBoxRadius) :
    Function.Surjective (boxOffAxisRowOfSum radius) := by
  rintro ⟨row, rowMembership⟩
  have bounds := (squareLatticeBoxOffAxisRows.mem_iff radius row).mp rowMembership
  have lower : -(radius.1 : ℤ) ≤ row := bounds.1
  have upper : row ≤ (radius.1 : ℤ) := bounds.2.1
  have nonzero : row ≠ 0 := bounds.2.2
  by_cases positive : 0 < row
  · let indexValue : ℕ := (row - 1).toNat
    have indexValue_cast : (indexValue : ℤ) = row - 1 := by
      exact Int.toNat_of_nonneg (by omega)
    have indexValue_lt : indexValue < radius.1 := by
      exact_mod_cast (show (indexValue : ℤ) < (radius.1 : ℤ) by omega)
    refine ⟨Sum.inl ⟨indexValue, indexValue_lt⟩, ?_⟩
    apply Subtype.ext
    simp [indexValue_cast]
  · have negative : row < 0 := by omega
    let indexValue : ℕ := (-row - 1).toNat
    have indexValue_cast : (indexValue : ℤ) = -row - 1 := by
      exact Int.toNat_of_nonneg (by omega)
    have indexValue_lt : indexValue < radius.1 := by
      exact_mod_cast (show (indexValue : ℤ) < (radius.1 : ℤ) by omega)
    refine ⟨Sum.inr ⟨indexValue, indexValue_lt⟩, ?_⟩
    apply Subtype.ext
    simp [indexValue_cast]

/-- Exact chain-index equivalence for off-axis horizontal rows. -/
def boxOffAxisRowEquiv (radius : PositiveSquareLatticeBoxRadius) :
    (Fin radius.1 ⊕ Fin radius.1) ≃ SquareLatticeBoxOffAxisRow radius :=
  Equiv.ofBijective (boxOffAxisRowOfSum radius)
    ⟨boxOffAxisRowOfSum_injective radius, boxOffAxisRowOfSum_surjective radius⟩

@[simp]
theorem boxOffAxisRowEquiv_inl (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowEquiv radius (Sum.inl index)).1 = (index.1 : ℤ) + 1 :=
  rfl

@[simp]
theorem boxOffAxisRowEquiv_inr (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowEquiv radius (Sum.inr index)).1 = -((index.1 : ℤ) + 1) :=
  rfl

/-- Explicit positive/negative-chain enumeration of all plaquette lower-left rows. -/
def boxPlaquetteRowOfSum (radius : PositiveSquareLatticeBoxRadius) :
    Fin radius.1 ⊕ Fin radius.1 → SquareLatticeBoxPlaquetteRow radius
  | Sum.inl index =>
      ⟨(index.1 : ℤ),
        (squareLatticeBoxInterval.mem_iff radius _).mpr (by
          have index_lt : (index.1 : ℤ) < (radius.1 : ℤ) := by exact_mod_cast index.2
          constructor <;> omega)⟩
  | Sum.inr index =>
      ⟨-((index.1 : ℤ) + 1),
        (squareLatticeBoxInterval.mem_iff radius _).mpr (by
          have index_lt : (index.1 : ℤ) < (radius.1 : ℤ) := by exact_mod_cast index.2
          constructor <;> omega)⟩

@[simp]
theorem boxPlaquetteRowOfSum_inl (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxPlaquetteRowOfSum radius (Sum.inl index)).1 = (index.1 : ℤ) :=
  rfl

@[simp]
theorem boxPlaquetteRowOfSum_inr (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxPlaquetteRowOfSum radius (Sum.inr index)).1 = -((index.1 : ℤ) + 1) :=
  rfl

private theorem boxPlaquetteRowOfSum_injective (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (boxPlaquetteRowOfSum radius) := by
  intro first second equality
  rcases first with first | first <;> rcases second with second | second
  · apply congrArg Sum.inl
    apply Fin.ext
    have values := congrArg Subtype.val equality
    simp only [boxPlaquetteRowOfSum_inl] at values
    exact_mod_cast values
  · have values := congrArg Subtype.val equality
    simp only [boxPlaquetteRowOfSum_inl, boxPlaquetteRowOfSum_inr] at values
    have first_nonneg : (0 : ℤ) ≤ first.1 := by exact_mod_cast Nat.zero_le first.1
    have second_nonneg : (0 : ℤ) ≤ second.1 := by exact_mod_cast Nat.zero_le second.1
    omega
  · have values := congrArg Subtype.val equality
    simp only [boxPlaquetteRowOfSum_inr, boxPlaquetteRowOfSum_inl] at values
    have first_nonneg : (0 : ℤ) ≤ first.1 := by exact_mod_cast Nat.zero_le first.1
    have second_nonneg : (0 : ℤ) ≤ second.1 := by exact_mod_cast Nat.zero_le second.1
    omega
  · apply congrArg Sum.inr
    apply Fin.ext
    have values := congrArg Subtype.val equality
    simp only [boxPlaquetteRowOfSum_inr] at values
    exact_mod_cast (show (first.1 : ℤ) = second.1 by omega)

private theorem boxPlaquetteRowOfSum_surjective (radius : PositiveSquareLatticeBoxRadius) :
    Function.Surjective (boxPlaquetteRowOfSum radius) := by
  rintro ⟨row, rowMembership⟩
  have bounds := (squareLatticeBoxInterval.mem_iff radius row).mp rowMembership
  have lower : -(radius.1 : ℤ) ≤ row := bounds.1
  have upper : row < (radius.1 : ℤ) := bounds.2
  by_cases nonnegative : 0 ≤ row
  · let indexValue : ℕ := row.toNat
    have indexValue_cast : (indexValue : ℤ) = row := Int.toNat_of_nonneg nonnegative
    have indexValue_lt : indexValue < radius.1 := by
      exact_mod_cast (show (indexValue : ℤ) < (radius.1 : ℤ) by omega)
    refine ⟨Sum.inl ⟨indexValue, indexValue_lt⟩, ?_⟩
    apply Subtype.ext
    simp [indexValue_cast]
  · have negative : row < 0 := by omega
    let indexValue : ℕ := (-row - 1).toNat
    have indexValue_cast : (indexValue : ℤ) = -row - 1 := by
      exact Int.toNat_of_nonneg (by omega)
    have indexValue_lt : indexValue < radius.1 := by
      exact_mod_cast (show (indexValue : ℤ) < (radius.1 : ℤ) by omega)
    refine ⟨Sum.inr ⟨indexValue, indexValue_lt⟩, ?_⟩
    apply Subtype.ext
    simp [indexValue_cast]

/-- Exact chain-index equivalence for plaquette lower-left rows. -/
def boxPlaquetteRowEquiv (radius : PositiveSquareLatticeBoxRadius) :
    (Fin radius.1 ⊕ Fin radius.1) ≃ SquareLatticeBoxPlaquetteRow radius :=
  Equiv.ofBijective (boxPlaquetteRowOfSum radius)
    ⟨boxPlaquetteRowOfSum_injective radius, boxPlaquetteRowOfSum_surjective radius⟩

@[simp]
theorem boxPlaquetteRowEquiv_inl (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxPlaquetteRowEquiv radius (Sum.inl index)).1 = (index.1 : ℤ) :=
  rfl

@[simp]
theorem boxPlaquetteRowEquiv_inr (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxPlaquetteRowEquiv radius (Sum.inr index)).1 = -((index.1 : ℤ) + 1) :=
  rfl

/-- Upper plaquette `i` lies immediately below positive horizontal row `i+1`. -/
@[simp]
theorem box_upper_row_alignment (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowEquiv radius (Sum.inl index)).1 =
      (boxPlaquetteRowEquiv radius (Sum.inl index)).1 + 1 := by
  simp

/-- Lower plaquette `i` has the same lower row as negative horizontal row `-(i+1)`. -/
@[simp]
theorem box_lower_row_alignment (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowEquiv radius (Sum.inr index)).1 =
      (boxPlaquetteRowEquiv radius (Sum.inr index)).1 := by
  simp

end

end YangMills.Dimensions
