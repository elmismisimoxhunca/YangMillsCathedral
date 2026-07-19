/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndexEnumeration

/-!
# Hostile probes for enumerated four-dimensional candidate multi-indices

These probes prevent multiplicities, occurrence order, and the underlying Schwartz test from being
replaced by disconnected data. Downstream modules prove permutation independence and then package
the canonical formal `D^α` at positive arity; these probes isolate the preceding combinatorial
all-enumeration comparison.
-/

namespace YangMills.OSOrderedFourDimensionalMultiIndexEnumeration.Probes

noncomputable section

/-- The induced multiplicity at coordinate `i` is exactly the cardinality of its tuple fiber. -/
theorem exact_tuple_multiplicity
    {n k : ℕ} (coordinates : Fin k → FourDimensionalPointCoordinateIndex n)
    (i : FourDimensionalFlatCoordinateIndex n) :
    fourDimensionalCoordinateTupleMultiIndex coordinates i =
      Fintype.card {j : Fin k //
        fourDimensionalPointCoordinateEquiv n (coordinates j) = i} :=
  rfl

/-- The constructed occurrence enumeration recovers each original ordered tuple entry exactly. -/
theorem exact_ordered_tuple_recovery
    {n k : ℕ} (coordinates : Fin k → FourDimensionalPointCoordinateIndex n)
    (j : Fin k) :
    fourDimensionalEnumeratedMultiIndexCoordinate
      (fourDimensionalCoordinateTupleEnumeration coordinates) j = coordinates j :=
  fourDimensionalCoordinateTupleEnumeration_recovers coordinates j

/-- The four-dimensional Fréchet condition and all-enumeration multi-index condition retain exactly
the same underlying Schwartz test. -/
theorem exact_frechet_enumerated_equivalence
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedDerivativeVanishing f ↔
      IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f :=
  osPositiveTimeOrderedFrechet_iff_enumeratedMultiIndex f

/-- The all-enumeration condition cannot omit the earlier canonical repeated-coordinate ordering. -/
theorem canonical_order_retained
    {n : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (h : IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f) :
    IsOSPositiveTimeOrderedMultiIndexVanishing f :=
  enumeratedMultiIndex_implies_canonical f h

/-- One nonzero arbitrary ordered coordinate jet outside strict order blocks the enumerated
multi-index condition; fiber multiplicities cannot hide the offending tuple. -/
theorem nonzero_ordered_coordinate_jet_blocked
    {n k : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (coordinates : Fin k → FourDimensionalPointCoordinateIndex n)
    (x : EuclideanNPointSpace EuclideanDimension.four n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four n)
    (hne : iteratedFDeriv ℝ k
      (f : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x
      (fun j => euclideanNPointCoordinateBasis EuclideanDimension.four n
        (coordinates j)) ≠ 0) :
    ¬ IsOSPositiveTimeOrderedEnumeratedMultiIndexVanishing f := by
  intro h
  apply hne
  simpa only [fourDimensionalCoordinateTupleEnumeration_recovers] using
    h (fourDimensionalCoordinateTupleMultiIndex coordinates) k
      (fourDimensionalCoordinateTupleEnumeration coordinates) x hx

/-- A nonzero arbitrary ordered exterior jet also blocks any accepted Fréchet-carrier surrogate
with the same underlying Schwartz function. -/
theorem nonzero_ordered_coordinate_jet_blocks_carrier
    {n k : ℕ} (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (coordinates : Fin k → FourDimensionalPointCoordinateIndex n)
    (x : EuclideanNPointSpace EuclideanDimension.four n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet EuclideanDimension.four n)
    (hne : iteratedFDeriv ℝ k
      (f : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x
      (fun j => euclideanNPointCoordinateBasis EuclideanDimension.four n
        (coordinates j)) ≠ 0) :
    ¬ ∃ accepted : OSPositiveTimeOrderedDerivativeCarrier EuclideanDimension.four n,
      accepted.toSchwartz = f := by
  rintro ⟨accepted, equality⟩
  apply nonzero_ordered_coordinate_jet_blocked f coordinates x hx hne
  rw [← equality]
  exact (osPositiveTimeOrderedFrechet_iff_enumeratedMultiIndex
    accepted.toSchwartz).mp accepted.2

end

end YangMills.OSOrderedFourDimensionalMultiIndexEnumeration.Probes
