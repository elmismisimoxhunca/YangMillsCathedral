/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndexEnumeration
import YangMills.Mathematics.SchwartzDirectionalPermutation

/-!
# Permutation independence of four-dimensional OS candidate multi-indices

Using the general permutation theorem for iterated Schwartz directional derivatives, this module
proves that any two occurrence enumerations of one four-dimensional multi-index give the same
candidate derivative. Every enumeration is then compared with the canonical occurrence ordering,
and canonical multi-index vanishing is proved equivalent both to all-enumeration vanishing and to
the original Fréchet candidate.

This closes the internal permutation/order-independence debt. It still does not identify the
canonical iterated-basis evaluation with OS-I printed p. 86's recursively interpreted coordinate
operator `D^α`; that final source-syntax comparison remains explicit debt. No exact OS source-space
identity, `(E2)`, reconstruction, theory inhabitant, or mass gap is asserted.
-/

namespace YangMills

noncomputable section

/-- Exact Euclidean configuration-basis tuple induced by an occurrence enumeration. -/
def fourDimensionalEnumeratedMultiIndexDirections
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (enumeration : FourDimensionalMultiIndexEnumeration α k) :
    Fin k → EuclideanNPointSpace EuclideanDimension.four n :=
  fun j => euclideanNPointCoordinateBasis EuclideanDimension.four n
    (fourDimensionalEnumeratedMultiIndexCoordinate enumeration j)

/-- Candidate derivative evaluated using an arbitrary exact occurrence enumeration. -/
def fourDimensionalEnumeratedMultiIndexDerivative
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (enumeration : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) : ℂ :=
  iteratedFDeriv ℝ k
    (f : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x
    (fourDimensionalEnumeratedMultiIndexDirections enumeration)

/-- Two occurrence enumerations differ by the exact slot permutation shown here. -/
theorem fourDimensionalEnumeratedMultiIndexDirections_eq_comp_perm
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (first second : FourDimensionalMultiIndexEnumeration α k) :
    fourDimensionalEnumeratedMultiIndexDirections second =
      fourDimensionalEnumeratedMultiIndexDirections first ∘
        (second.symm.trans first : Equiv.Perm (Fin k)) := by
  funext j
  simp [fourDimensionalEnumeratedMultiIndexDirections,
    fourDimensionalEnumeratedMultiIndexCoordinate]

/-- Any two occurrence enumerations with the same slot type give exactly the same derivative value
on the same Schwartz function and point. -/
theorem fourDimensionalEnumeratedMultiIndexDerivative_eq
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (first second : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    fourDimensionalEnumeratedMultiIndexDerivative first f x =
      fourDimensionalEnumeratedMultiIndexDerivative second f x := by
  unfold fourDimensionalEnumeratedMultiIndexDerivative
  rw [fourDimensionalEnumeratedMultiIndexDirections_eq_comp_perm first second]
  exact (SchwartzMap.iteratedFDeriv_comp_perm
    (fourDimensionalEnumeratedMultiIndexDirections first)
    (second.symm.trans first) f x).symm

/-- Every occurrence enumeration has `|α|` slots and evaluates to the earlier canonical candidate
multi-index derivative. The slot equality is derived from the actual equivalence. -/
theorem fourDimensionalEnumeratedMultiIndexDerivative_eq_canonical
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (enumeration : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    fourDimensionalEnumeratedMultiIndexDerivative enumeration f x =
      fourDimensionalMultiIndexDerivative α f x := by
  have hk : k = fourDimensionalMultiIndexOrder α := by
    simpa using Fintype.card_congr
      (enumeration.symm.trans (fourDimensionalMultiIndexOccurrenceEquiv α))
  subst k
  exact fourDimensionalEnumeratedMultiIndexDerivative_eq
    enumeration (fourDimensionalMultiIndexOccurrenceEquiv α) f x

/-- Canonical multi-index vanishing is equivalent to vanishing for every occurrence enumeration. -/
theorem osPositiveTimeOrderedCanonicalMultiIndex_iff_enumeratedMultiIndex
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedMultiIndexVanishing f ↔
      IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f := by
  constructor
  · intro h α k enumeration x hx
    change fourDimensionalEnumeratedMultiIndexDerivative enumeration f x = 0
    rw [fourDimensionalEnumeratedMultiIndexDerivative_eq_canonical]
    exact h α x hx
  · exact enumeratedMultiIndex_implies_canonical f

/-- In exactly four dimensions, the original Fréchet candidate is equivalent to the one canonical
multi-index ordering, now that occurrence-order independence is proved. -/
theorem osPositiveTimeOrderedFrechet_iff_canonicalMultiIndex
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedDerivativeVanishing f ↔
      IsOSPositiveTimeOrderedMultiIndexVanishing f := by
  rw [osPositiveTimeOrderedFrechet_iff_enumeratedMultiIndex,
    ← osPositiveTimeOrderedCanonicalMultiIndex_iff_enumeratedMultiIndex]

end

end YangMills
