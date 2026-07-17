/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean spacetime dimensions used by the Yang–Mills checker

This module introduces only dimension bookkeeping. `EuclideanDimension` ranges from one through
four, inclusive. It does not identify Euclidean and Minkowski objects, choose a time coordinate, or
assert an Osterwalder–Schrader reconstruction.

The four-dimensional endpoint is required by the Clay/Jaffe–Witten problem statement, PDF p. 6,
§4. Dimensions one through three are project-level consistency regimes; they are not part of the
Clay quantifier and do not imply the four-dimensional contract.
-/

namespace YangMills

/-- A Euclidean spacetime dimension supported by this checker: exactly `1`, `2`, `3`, or `4`.

This is dimension of spacetime, not dimension of a spatial slice. -/
structure EuclideanDimension where
  /-- The underlying natural-number dimension. -/
  value : ℕ
  /-- Zero-dimensional spacetime is outside the public checker. -/
  one_le : 1 ≤ value
  /-- The project studies dimensions only through the four-dimensional Clay endpoint. -/
  le_four : value ≤ 4
  deriving DecidableEq

namespace EuclideanDimension

/-- Euclidean spacetime dimension one. -/
def one : EuclideanDimension := ⟨1, by decide, by decide⟩

/-- Euclidean spacetime dimension two. -/
def two : EuclideanDimension := ⟨2, by decide, by decide⟩

/-- Euclidean spacetime dimension three. -/
def three : EuclideanDimension := ⟨3, by decide, by decide⟩

/-- Euclidean spacetime dimension four, the dimension in the Clay/Jaffe–Witten statement. -/
def four : EuclideanDimension := ⟨4, by decide, by decide⟩

@[simp] theorem one_value : one.value = 1 := rfl
@[simp] theorem two_value : two.value = 2 := rfl
@[simp] theorem three_value : three.value = 3 := rfl
@[simp] theorem four_value : four.value = 4 := rfl

/-- Spatial dimension associated to a Euclidean dimension after selecting one coordinate as time.

This arithmetic definition does not itself perform or assume reconstruction. -/
def spatialDimension (d : EuclideanDimension) : ℕ := d.value - 1

@[simp] theorem one_spatialDimension : one.spatialDimension = 0 := rfl
@[simp] theorem two_spatialDimension : two.spatialDimension = 1 := rfl
@[simp] theorem three_spatialDimension : three.spatialDimension = 2 := rfl
@[simp] theorem four_spatialDimension : four.spatialDimension = 3 := rfl

/-- A supported Euclidean dimension can never be zero. -/
theorem value_ne_zero (d : EuclideanDimension) : d.value ≠ 0 :=
  Nat.ne_of_gt d.one_le

/-- Every supported dimension is one of the four named dimensions. -/
theorem eq_one_or_eq_two_or_eq_three_or_eq_four (d : EuclideanDimension) :
    d = one ∨ d = two ∨ d = three ∨ d = four := by
  rcases d with ⟨value, one_le, le_four⟩
  interval_cases value <;> simp_all [one, two, three, four]

/-- The coordinate-index type of Euclidean spacetime of dimension `d`. -/
abbrev CoordinateIndex (d : EuclideanDimension) := Fin d.value

/-- Mathlib's real Euclidean coordinate space in spacetime dimension `d`. -/
abbrev Spacetime (d : EuclideanDimension) := EuclideanSpace ℝ d.CoordinateIndex

/-- The coordinate-index type is nonempty because supported dimensions are positive. -/
instance (d : EuclideanDimension) : Nonempty d.CoordinateIndex :=
  Fin.pos_iff_nonempty.mp d.one_le

/-- The real vector-space dimension agrees with the declared Euclidean spacetime dimension. -/
@[simp] theorem finrank_spacetime (d : EuclideanDimension) :
    Module.finrank ℝ d.Spacetime = d.value := by
  simp [Spacetime, CoordinateIndex]

/-- Distinct named dimensions are distinct checker indices. -/
theorem two_ne_four : two ≠ four := by
  intro equality
  have := congrArg EuclideanDimension.value equality
  simp at this

end EuclideanDimension

end YangMills
