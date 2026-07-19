/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedCoordinateJets

/-!
# Four-dimensional multi-index coordinates for the OS ordered candidate

Osterwalder–Schrader I, printed p. 86, writes `D^α` for coordinate partial derivatives on
`ℝ^(4n)` and requires them to vanish outside strict time order. This module begins the exact
four-dimensional comparison by flattening a point/coordinate pair `(i, μ)` to the point-major
index `μ + 4 i`, defining natural-valued multi-indices on `Fin (4n)`, and constructing an exact
finite occurrence enumeration with each coordinate repeated according to its multiplicity.

The resulting derivative is deliberately called a **candidate multi-index derivative**. Downstream
modules quantify over exact occurrence enumerations, recover arbitrary coordinate tuples, and prove
permutation independence, yielding an internal converse to the implication exposed here. Its
identification with the source's recursively interpreted `D^α` is supplied only by a downstream
source-space module after those theorems, not by this initial definition. No reflection positivity,
reconstruction, theory inhabitant, or mass-gap claim is asserted.
-/

namespace YangMills

open scoped BigOperators

noncomputable section

/-- Point/coordinate labels for an `n`-point configuration in exactly four Euclidean dimensions. -/
abbrev FourDimensionalPointCoordinateIndex (n : ℕ) :=
  ((_point : Fin n) × EuclideanDimension.four.CoordinateIndex)

/-- Flattened point-major coordinate index for `ℝ^(4n)`. -/
abbrev FourDimensionalFlatCoordinateIndex (n : ℕ) := Fin (n * 4)

/-- A natural-valued multi-index on the exact flattened four-dimensional configuration. -/
abbrev FourDimensionalMultiIndex (n : ℕ) := FourDimensionalFlatCoordinateIndex n → ℕ

/-- Exact point-major flattening `(i, μ) ↦ μ + 4i`. -/
def fourDimensionalPointCoordinateEquiv (n : ℕ) :
    FourDimensionalPointCoordinateIndex n ≃ FourDimensionalFlatCoordinateIndex n :=
  (Equiv.sigmaEquivProd (Fin n) EuclideanDimension.four.CoordinateIndex).trans
    finProdFinEquiv

/-- The flattening has the explicit project point-major arithmetic convention matching the
source's displayed point blocks `x₁, …, xₙ`. -/
@[simp]
theorem fourDimensionalPointCoordinateEquiv_apply
    (n : ℕ) (point : Fin n) (coordinate : EuclideanDimension.four.CoordinateIndex) :
    (fourDimensionalPointCoordinateEquiv n ⟨point, coordinate⟩).val =
      coordinate.val + 4 * point.val := by
  rfl

/-- Total order `|α|` of a four-dimensional multi-index. -/
def fourDimensionalMultiIndexOrder {n : ℕ} (α : FourDimensionalMultiIndex n) : ℕ :=
  ∑ i, α i

/-- Exact equivalence between coordinate occurrences `(i, r)` with `r < αᵢ` and the `|α|`
derivative slots. -/
def fourDimensionalMultiIndexOccurrenceEquiv {n : ℕ} (α : FourDimensionalMultiIndex n) :
    ((i : FourDimensionalFlatCoordinateIndex n) × Fin (α i)) ≃
      Fin (fourDimensionalMultiIndexOrder α) :=
  finSigmaFinEquiv

/-- The flattened coordinate selected by each canonical occurrence slot. -/
def fourDimensionalMultiIndexRepeatedCoordinate {n : ℕ} (α : FourDimensionalMultiIndex n) :
    Fin (fourDimensionalMultiIndexOrder α) → FourDimensionalPointCoordinateIndex n :=
  fun j => (fourDimensionalPointCoordinateEquiv n).symm
    ((fourDimensionalMultiIndexOccurrenceEquiv α).symm j).1

/-- The exact Euclidean configuration-basis direction selected at each occurrence slot. -/
def fourDimensionalMultiIndexDirections {n : ℕ} (α : FourDimensionalMultiIndex n) :
    Fin (fourDimensionalMultiIndexOrder α) →
      EuclideanNPointSpace EuclideanDimension.four n :=
  fun j => euclideanNPointCoordinateBasis EuclideanDimension.four n
    (fourDimensionalMultiIndexRepeatedCoordinate α j)

/-- Every occurrence of flattened coordinate `i` maps back to exactly `i`, independently of its
multiplicity label. -/
@[simp]
theorem fourDimensionalMultiIndexRepeatedCoordinate_occurrence
    {n : ℕ} (α : FourDimensionalMultiIndex n)
    (i : FourDimensionalFlatCoordinateIndex n) (r : Fin (α i)) :
    fourDimensionalMultiIndexRepeatedCoordinate α
      (fourDimensionalMultiIndexOccurrenceEquiv α ⟨i, r⟩) =
      (fourDimensionalPointCoordinateEquiv n).symm i := by
  simp [fourDimensionalMultiIndexRepeatedCoordinate]

/-- Every occurrence slot evaluates along the exact basis direction of its flattened coordinate. -/
@[simp]
theorem fourDimensionalMultiIndexDirections_occurrence
    {n : ℕ} (α : FourDimensionalMultiIndex n)
    (i : FourDimensionalFlatCoordinateIndex n) (r : Fin (α i)) :
    fourDimensionalMultiIndexDirections α
      (fourDimensionalMultiIndexOccurrenceEquiv α ⟨i, r⟩) =
      euclideanNPointCoordinateBasis EuclideanDimension.four n
        ((fourDimensionalPointCoordinateEquiv n).symm i) := by
  simp [fourDimensionalMultiIndexDirections]

/-- Candidate `D^α` evaluation defined from the exact repeated coordinate directions. -/
def fourDimensionalMultiIndexDerivative
    {n : ℕ} (α : FourDimensionalMultiIndex n)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) : ℂ :=
  iteratedFDeriv ℝ (fourDimensionalMultiIndexOrder α)
    (f : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x
    (fourDimensionalMultiIndexDirections α)

/-- Candidate four-dimensional multi-index exterior-vanishing condition. -/
def IsOSPositiveTimeOrderedMultiIndexVanishing
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) : Prop :=
  ∀ α : FourDimensionalMultiIndex n,
    ∀ x : EuclideanNPointSpace EuclideanDimension.four n,
      x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four n →
        fourDimensionalMultiIndexDerivative α f x = 0

/-- The established Fréchet candidate implies every canonical four-dimensional candidate
multi-index derivative vanishes. This initial module exposes only that direction; downstream
multiplicity, enumeration and permutation modules prove the converse, and the positive-arity
source-space layer supplies the formal `D^α` interpretation. -/
theorem frechet_implies_fourDimensionalMultiIndexVanishing
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (h : IsOSPositiveTimeOrderedDerivativeVanishing f) :
    IsOSPositiveTimeOrderedMultiIndexVanishing f := by
  rw [osPositiveTimeOrderedFrechet_iff_coordinateJets] at h
  intro α x hx
  exact h (fourDimensionalMultiIndexOrder α) x hx
    (fun j => fourDimensionalMultiIndexRepeatedCoordinate α j)

end

end YangMills
