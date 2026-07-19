/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndex

/-!
# Hostile probes for four-dimensional OS candidate multi-indices

The probes lock exact four-dimensional scope, point-major flattening, occurrence multiplicity,
derivative evaluation, zero total order, and the one-way bridge exposed by this initial module.
Downstream modules prove the converse and permutation independence and then package the formal
OS-I `D^α` interpretation only at positive arity.
-/

namespace YangMills.OSOrderedFourDimensionalMultiIndex.Probes

noncomputable section

/-- Flattening retains both the point label and spacetime coordinate in point-major order. -/
theorem exact_point_major_flattening
    (n : ℕ) (point : Fin n) (coordinate : EuclideanDimension.four.CoordinateIndex) :
    (fourDimensionalPointCoordinateEquiv n ⟨point, coordinate⟩).val =
      coordinate.val + 4 * point.val :=
  fourDimensionalPointCoordinateEquiv_apply n point coordinate

/-- Every one of the `αᵢ` named occurrences selects the exact same flattened coordinate `i`. -/
theorem exact_multiplicity_occurrence
    {n : ℕ} (α : FourDimensionalMultiIndex n)
    (i : FourDimensionalFlatCoordinateIndex n) (r : Fin (α i)) :
    (fourDimensionalPointCoordinateEquiv n)
      (fourDimensionalMultiIndexRepeatedCoordinate α
        (fourDimensionalMultiIndexOccurrenceEquiv α ⟨i, r⟩)) = i := by
  simp

/-- The candidate multi-index derivative is tied definitionally to the exact iterated Fréchet
derivative and repeated direction tuple, preventing a constant-zero replacement. -/
theorem exact_multiIndex_derivative_value
    {n : ℕ} (α : FourDimensionalMultiIndex n)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    fourDimensionalMultiIndexDerivative α f x =
      iteratedFDeriv ℝ (fourDimensionalMultiIndexOrder α)
        (f : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x
        (fourDimensionalMultiIndexDirections α) :=
  rfl

/-- The unique zero-arity multi-index evaluates as the exact order-zero derivative, hence as the
underlying Schwartz value. -/
theorem zero_arity_multiIndex_derivative
    (α : FourDimensionalMultiIndex 0)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four 0)
    (x : EuclideanNPointSpace EuclideanDimension.four 0) :
    fourDimensionalMultiIndexDerivative α f x = f x := by
  have hα : α = fun i => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  subst α
  change (iteratedFDeriv ℝ 0
    (f : EuclideanNPointSpace EuclideanDimension.four 0 → ℂ) x) _ = f x
  exact iteratedFDeriv_zero_apply _

/-- The zero multi-index has total derivative order zero. -/
theorem zero_multiIndex_order {n : ℕ} :
    fourDimensionalMultiIndexOrder
      (fun _ : FourDimensionalFlatCoordinateIndex n => 0) = 0 := by
  simp [fourDimensionalMultiIndexOrder]

/-- An accepted Fréchet-carrier test satisfies every canonical four-dimensional multi-index
vanishing condition on the same underlying Schwartz function. -/
theorem exact_frechet_to_multiIndex_bridge
    {n : ℕ} (f : OSPositiveTimeOrderedDerivativeCarrier EuclideanDimension.four n) :
    IsOSPositiveTimeOrderedMultiIndexVanishing f.toSchwartz :=
  frechet_implies_fourDimensionalMultiIndexVanishing f.toSchwartz f.2

/-- A nonzero candidate multi-index derivative outside strict order blocks membership in the exact
Fréchet carrier; the multi-index datum cannot be disconnected from the accepted test. -/
theorem nonzero_multiIndex_exterior_jet_blocked
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
  exact exact_frechet_to_multiIndex_bridge accepted α x hx

end

end YangMills.OSOrderedFourDimensionalMultiIndex.Probes
