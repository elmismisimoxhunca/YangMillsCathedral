/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndex

/-!
# Enumerations of four-dimensional OS candidate multi-indices

A natural-valued multi-index records multiplicity but not an ordering of derivative slots. This
module separates those notions explicitly. An enumeration is an equivalence from the dependent sum
of the `αᵢ` coordinate occurrences to `Fin k`. Every ordered coordinate tuple produces a
multi-index by taking exact fiber cardinalities and an enumeration through
`Equiv.sigmaFiberEquiv`; the induced enumerated coordinates are proved to recover the original
tuple exactly.

Quantifying candidate vanishing over every enumeration is therefore proved equivalent to the
existing all-coordinate-tuple Fréchet candidate. This is a combinatorial comparison, not yet a
proof that the canonical repeated-basis derivative is invariant under permutations, nor an
identification with OS-I printed p. 86's recursively interpreted `D^α`. Those analytic/source
comparisons remain explicit debt. No `(E2)`, reconstruction, theory inhabitant, or mass gap is
asserted.
-/

namespace YangMills

noncomputable section

/-- An ordering of all occurrences of a multi-index into exactly `k` derivative slots. Existence of
this equivalence itself forces `k = |α|`, without storing a disconnected cardinality equation. -/
abbrev FourDimensionalMultiIndexEnumeration {n : ℕ}
    (α : FourDimensionalMultiIndex n) (k : ℕ) :=
  ((i : FourDimensionalFlatCoordinateIndex n) × Fin (α i)) ≃ Fin k

/-- Multiplicity multi-index induced by an arbitrary ordered point/coordinate tuple: `αᵢ` is the
exact cardinality of the fiber over flattened coordinate `i`. -/
def fourDimensionalCoordinateTupleMultiIndex {n k : ℕ}
    (coordinates : Fin k → FourDimensionalPointCoordinateIndex n) :
    FourDimensionalMultiIndex n :=
  fun i => Fintype.card {j : Fin k //
    fourDimensionalPointCoordinateEquiv n (coordinates j) = i}

/-- Exact enumeration of the fiber-cardinality multi-index induced by an ordered coordinate tuple. -/
def fourDimensionalCoordinateTupleEnumeration {n k : ℕ}
    (coordinates : Fin k → FourDimensionalPointCoordinateIndex n) :
    FourDimensionalMultiIndexEnumeration
      (fourDimensionalCoordinateTupleMultiIndex coordinates) k :=
  (Equiv.sigmaCongrRight fun i =>
    (Fintype.equivFin {j : Fin k //
      fourDimensionalPointCoordinateEquiv n (coordinates j) = i}).symm).trans
    (Equiv.sigmaFiberEquiv fun j =>
      fourDimensionalPointCoordinateEquiv n (coordinates j))

/-- Point/coordinate tuple induced by a supplied occurrence enumeration. -/
def fourDimensionalEnumeratedMultiIndexCoordinate
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (enumeration : FourDimensionalMultiIndexEnumeration α k) :
    Fin k → FourDimensionalPointCoordinateIndex n :=
  fun j => (fourDimensionalPointCoordinateEquiv n).symm (enumeration.symm j).1

/-- Fiber-cardinality enumeration recovers every entry of the original ordered coordinate tuple
exactly, including repetitions and order. -/
@[simp]
theorem fourDimensionalCoordinateTupleEnumeration_recovers
    {n k : ℕ} (coordinates : Fin k → FourDimensionalPointCoordinateIndex n) (j : Fin k) :
    fourDimensionalEnumeratedMultiIndexCoordinate
      (fourDimensionalCoordinateTupleEnumeration coordinates) j = coordinates j := by
  let flat := fun j => fourDimensionalPointCoordinateEquiv n (coordinates j)
  let fibers := fun i => {j : Fin k // flat j = i}
  let firstEquiv : ((i : FourDimensionalFlatCoordinateIndex n) ×
      Fin (Fintype.card (fibers i))) ≃
        ((i : FourDimensionalFlatCoordinateIndex n) × fibers i) :=
    Equiv.sigmaCongrRight fun i => (Fintype.equivFin (fibers i)).symm
  let totalEquiv := firstEquiv.trans (Equiv.sigmaFiberEquiv flat)
  let p := totalEquiv.symm j
  have hp : totalEquiv p = j := totalEquiv.apply_symm_apply j
  have fiber_property : flat ((firstEquiv p).2 : Fin k) = (firstEquiv p).1 :=
    (firstEquiv p).2.property
  have hfirst : p.1 = flat j := by
    calc
      p.1 = flat ((firstEquiv p).2 : Fin k) := fiber_property.symm
      _ = flat (totalEquiv p) := rfl
      _ = flat j := congrArg flat hp
  have hfirstActual :
      ((fourDimensionalCoordinateTupleEnumeration coordinates).symm j).1 =
        fourDimensionalPointCoordinateEquiv n (coordinates j) := by
    change p.1 = flat j
    exact hfirst
  apply (fourDimensionalPointCoordinateEquiv n).injective
  simpa [fourDimensionalEnumeratedMultiIndexCoordinate] using hfirstActual

/-- Candidate exterior vanishing for every multi-index and every exact occurrence enumeration. -/
def IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) : Prop :=
  ∀ (α : FourDimensionalMultiIndex n) (k : ℕ)
    (enumeration : FourDimensionalMultiIndexEnumeration α k),
    ∀ x : EuclideanNPointSpace EuclideanDimension.four n,
      x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four n →
      iteratedFDeriv ℝ k
        (f : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x
        (fun j => euclideanNPointCoordinateBasis EuclideanDimension.four n
          (fourDimensionalEnumeratedMultiIndexCoordinate enumeration j)) = 0

/-- Vanishing for every occurrence enumeration includes the earlier canonical enumeration. -/
theorem enumeratedMultiIndex_implies_canonical
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (h : IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f) :
    IsOSPositiveTimeOrderedMultiIndexVanishing f := by
  intro α x hx
  exact h α (fourDimensionalMultiIndexOrder α)
    (fourDimensionalMultiIndexOccurrenceEquiv α) x hx

/-- All ordered coordinate-jet vanishing is exactly equivalent to all enumerated multi-index
vanishing. The reverse direction uses fiber cardinalities and exact tuple recovery, not an assumed
permutation theorem. -/
theorem osPositiveTimeOrderedCoordinateJets_iff_enumeratedMultiIndex
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedCoordinateJetVanishing f ↔
      IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f := by
  constructor
  · intro h α k enumeration x hx
    exact h k x hx (fourDimensionalEnumeratedMultiIndexCoordinate enumeration)
  · intro h k x hx coordinates
    simpa only [fourDimensionalCoordinateTupleEnumeration_recovers] using
      h (fourDimensionalCoordinateTupleMultiIndex coordinates) k
        (fourDimensionalCoordinateTupleEnumeration coordinates) x hx

/-- In exactly four dimensions, the original full Fréchet candidate is equivalent to candidate
vanishing for every multi-index occurrence enumeration. This still does not identify one canonical
ordering with source `D^α`. -/
theorem osPositiveTimeOrderedFrechet_iff_enumeratedMultiIndex
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedDerivativeVanishing f ↔
      IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f := by
  rw [osPositiveTimeOrderedFrechet_iff_coordinateJets,
    osPositiveTimeOrderedCoordinateJets_iff_enumeratedMultiIndex]

end

end YangMills
