/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndexPermutation

/-!
# Hostile probes for four-dimensional multi-index permutation independence

These probes lock order independence to actual occurrence enumerations, the exact same Schwartz
function and point, and the earlier canonical derivative. They do not identify that derivative with
OS-I's still-uncompared recursive `D^α` syntax.
-/

namespace YangMills.OSOrderedFourDimensionalMultiIndexPermutation.Probes

noncomputable section

/-- The exact slot permutation relating two occurrence enumerations is retained. -/
theorem exact_enumeration_slot_permutation
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (first second : FourDimensionalMultiIndexEnumeration α k) :
    fourDimensionalEnumeratedMultiIndexDirections second =
      fourDimensionalEnumeratedMultiIndexDirections first ∘
        (second.symm.trans first : Equiv.Perm (Fin k)) :=
  fourDimensionalEnumeratedMultiIndexDirections_eq_comp_perm first second

/-- Enumeration order cannot change the exact derivative value. -/
theorem exact_enumeration_independence
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (first second : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    fourDimensionalEnumeratedMultiIndexDerivative first f x =
      fourDimensionalEnumeratedMultiIndexDerivative second f x :=
  fourDimensionalEnumeratedMultiIndexDerivative_eq first second f x

/-- Every enumeration evaluates to the same earlier canonical derivative, with no disconnected
cardinality or value witness. -/
theorem exact_canonical_value
    {n k : ℕ} {α : FourDimensionalMultiIndex n}
    (enumeration : FourDimensionalMultiIndexEnumeration α k)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    fourDimensionalEnumeratedMultiIndexDerivative enumeration f x =
      fourDimensionalMultiIndexDerivative α f x :=
  fourDimensionalEnumeratedMultiIndexDerivative_eq_canonical enumeration f x

/-- The canonical and all-enumeration vanishing predicates are exactly equivalent. -/
theorem exact_canonical_enumerated_equivalence
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedMultiIndexVanishing f ↔
      IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f :=
  osPositiveTimeOrderedCanonicalMultiIndex_iff_enumeratedMultiIndex f

/-- The original Fréchet candidate is exactly equivalent to the canonical four-dimensional
multi-index condition after proving order independence. -/
theorem exact_frechet_canonical_equivalence
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedDerivativeVanishing f ↔
      IsOSPositiveTimeOrderedMultiIndexVanishing f :=
  osPositiveTimeOrderedFrechet_iff_canonicalMultiIndex f

/-- One nonzero canonical exterior derivative blocks every accepted Fréchet-carrier surrogate with
the same underlying Schwartz function. -/
theorem nonzero_canonical_exterior_jet_blocks_carrier
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n)
    (x : EuclideanNPointSpace EuclideanDimension.four n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four n)
    (hne : fourDimensionalMultiIndexDerivative α f x ≠ 0) :
    ¬ ∃ accepted : OSPositiveTimeOrderedDerivativeCarrier EuclideanDimension.four n,
      accepted.toSchwartz = f := by
  rintro ⟨accepted, equality⟩
  apply hne
  rw [← equality]
  exact (osPositiveTimeOrderedFrechet_iff_canonicalMultiIndex
    accepted.toSchwartz).mp accepted.2 α x hx

end

end YangMills.OSOrderedFourDimensionalMultiIndexPermutation.Probes
