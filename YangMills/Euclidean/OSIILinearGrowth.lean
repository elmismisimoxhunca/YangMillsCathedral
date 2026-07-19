/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpace
import YangMills.Euclidean.SchwingerRegularity

/-!
# OS-II linear-growth acceptance strengthening with an ambient tempered extension

OS-II printed p. 284 equation (2.1) uses the weighted multi-index Schwartz norm

`|f|ₚ = sup_{x, |α| ≤ p} (1 + |x|²)^(p/2) |D^α f(x)|`,

and printed p. 287 equation (4.1) requires one positive order `s` and factorial-growth coefficients
`σₙ` such that `|Sₙ(f)| ≤ σₙ |f|ₛ` for every positive arity.

This module characterizes the displayed supremum by its upper-bound/least-upper-bound universal
property rather than identifying it with Mathlib's different Fréchet seminorm presentation. Equation
(4.1) is imposed only on the exact coincidence-flat `𝒮₀` subtype. The surrounding Schwinger family
still supplies ambient tempered extensions on full Schwartz space, so the final record is explicitly
a strengthening of source `(E0′)`, not yet its carrier-exact formulation. No Schwinger family or
reconstruction is constructed.
-/

namespace YangMills

noncomputable section

/-- The zero four-dimensional multi-index. -/
def zeroFourDimensionalMultiIndex (n : ℕ) : FourDimensionalMultiIndex n :=
  fun _ => 0

@[simp] theorem zeroFourDimensionalMultiIndex_order (n : ℕ) :
    fourDimensionalMultiIndexOrder (zeroFourDimensionalMultiIndex n) = 0 := by
  simp [zeroFourDimensionalMultiIndex, fourDimensionalMultiIndexOrder]

/-- Exact flattened Euclidean coordinate square `x² = ∑ᵢ∑μ (xᵢ^μ)²` on `ℝ^(4n)`.

The outer function-space norm on `Fin n → ℝ⁴` is a supremum norm and must not be used here. -/
def fourDimensionalConfigurationSquaredNorm
    {n : ℕ} (x : EuclideanNPointSpace EuclideanDimension.four n) : ℝ :=
  ∑ i, ∑ μ, (x i μ) ^ 2

/-- One term in OS-II's printed weighted multi-index norm at order `p`. -/
noncomputable def osIIPrintedWeightedDerivativeTerm
    {n : ℕ} (p : ℕ) (α : FourDimensionalMultiIndex n)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) : ℝ :=
  Real.rpow (1 + fourDimensionalConfigurationSquaredNorm x) ((p : ℝ) / 2) *
    ‖fourDimensionalMultiIndexDerivative α f x‖

/-- Exact least-upper-bound presentation of OS-II's displayed Schwartz norm at one arity/order.

The value is supplied but fully characterized by all points and all multi-indices of total order at
most `p`; an unrelated control function cannot satisfy the universal property. -/
structure OSIIPrintedSchwartzControlData (n p : ℕ) where
  /-- The source's displayed `|f|ₚ`. -/
  control : ScalarSchwartzTestFunction EuclideanDimension.four n → ℝ
  /-- The displayed supremum is nonnegative. -/
  control_nonnegative : ∀ f, 0 ≤ control f
  /-- Every printed weighted derivative term of order at most `p` is bounded by the control. -/
  weightedDerivative_le : ∀ (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n),
    fourDimensionalMultiIndexOrder α ≤ p → ∀ x,
      osIIPrintedWeightedDerivativeTerm p α f x ≤ control f
  /-- The control is the least common upper bound of those exact terms. -/
  control_le_of_weightedDerivative_le : ∀
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n) (bound : ℝ),
    (∀ (α : FourDimensionalMultiIndex n),
      fourDimensionalMultiIndexOrder α ≤ p → ∀ x,
        osIIPrintedWeightedDerivativeTerm p α f x ≤ bound) →
    control f ≤ bound

namespace OSIIPrintedSchwartzControlData

/-- The least-upper-bound characterization uniquely determines the printed control. -/
theorem control_unique
    {n p : ℕ} (first second : OSIIPrintedSchwartzControlData n p) :
    first.control = second.control := by
  funext f
  apply le_antisymm
  · exact first.control_le_of_weightedDerivative_le f (second.control f)
      (second.weightedDerivative_le f)
  · exact second.control_le_of_weightedDerivative_le f (first.control f)
      (first.weightedDerivative_le f)

/-- The exact printed control of the zero Schwartz test is zero. -/
@[simp] theorem control_zero
    {n p : ℕ} (data : OSIIPrintedSchwartzControlData n p) :
    data.control 0 = 0 := by
  apply le_antisymm
  · apply data.control_le_of_weightedDerivative_le
    intro α _ x
    change Real.rpow (1 + fourDimensionalConfigurationSquaredNorm x) ((p : ℝ) / 2) *
      ‖(iteratedFDeriv ℝ (fourDimensionalMultiIndexOrder α)
        (0 : EuclideanNPointSpace EuclideanDimension.four n → ℂ) x)
        (fourDimensionalMultiIndexDirections α)‖ ≤ 0
    rw [iteratedFDeriv_zero]
    simp
  · exact data.control_nonnegative 0

/-- Any strictly positive displayed derivative term forces the exact printed control to be nonzero. -/
theorem control_ne_zero_of_term_pos
    {n p : ℕ} (data : OSIIPrintedSchwartzControlData n p)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n) (order_le : fourDimensionalMultiIndexOrder α ≤ p)
    (x : EuclideanNPointSpace EuclideanDimension.four n)
    (term_pos : 0 < osIIPrintedWeightedDerivativeTerm p α f x) :
    data.control f ≠ 0 := by
  intro control_zero
  have bound := data.weightedDerivative_le f α order_le x
  rw [control_zero] at bound
  exact (not_lt_of_ge bound) term_pos

end OSIIPrintedSchwartzControlData

/-- The exact OS-II coincidence-flat test carrier `𝒮₀(ℝ^(4n))`. -/
abbrev OSIICoincidenceFlatSchwartzTestFunction (n : ℕ) :=
  {f : ScalarSchwartzTestFunction EuclideanDimension.four n // IsFlatAtPointCoincidences f}

/-- OS-II `(E0′)` linear growth on `𝒮₀`, with a separately supplied ambient tempered extension.

The ambient full-Schwartz family is extra strengthening data and prevents this record from being the
final carrier-exact source formulation. -/
structure OSIIAmbientExtensionLinearGrowthData
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.four) where
  /-- One common positive Schwartz order for every arity. -/
  order : ℕ
  order_positive : 0 < order
  /-- Positive factorial-growth coefficients `σₙ`. -/
  growth : FactorialGrowthSequence
  /-- Exact printed Schwartz control at every positive arity and that same order. -/
  printedControl : ∀ n : PositiveArity, OSIIPrintedSchwartzControlData n.value order
  /-- Equation (4.1) on the exact coincidence-flat `𝒮₀` carrier, evaluated through the same
  ambient tempered extension. -/
  bound : ∀ (n : PositiveArity)
    (f : OSIICoincidenceFlatSchwartzTestFunction n.value),
    ‖family.positivePoint n f.1‖ ≤ growth.coefficient n * (printedControl n).control f.1

end

end YangMills
