/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Dimensions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar Schwinger-distribution regularity infrastructure

This module packages scalar, positive-arity tempered distributions on actual Mathlib Schwartz
spaces and a concrete fixed-order factorial-growth estimate. It is preparatory infrastructure for
the Euclidean Yang–Mills acceptance surface; it is not an Osterwalder–Schrader theory and does not
state covariance, reflection positivity, symmetry, clustering, or reconstruction.

Osterwalder–Schrader I, printed pp. 86–88, defines its test spaces and axioms `(E0)`–`(E4)`.
Osterwalder–Schrader II, printed p. 287, replaces ordinary temperedness by the linear-growth
condition `(E0′)`: one fixed Schwartz order and coefficients of factorial growth control every
arity. The concrete control below is a finite sum of Mathlib's weighted Fréchet-derivative Schwartz
seminorms. It is deliberately named `MathlibFixedOrderFactorialGrowthData`, not
`OSIILinearGrowthData`: a later bridge must compare this full-Schwartz-space convention with the
paper's diagonal-sensitive test space and weighted multi-index norm while preserving factorial
growth.
-/

open scoped SchwartzMap

namespace YangMills

/-- A strictly positive correlation-function arity.

Keeping the value and positivity proof together prevents the common predecessor-index error in
factorial bounds. -/
structure PositiveArity where
  /-- The actual number of Euclidean points. -/
  value : ℕ
  /-- Positive-point distributions never use arity zero. -/
  positive : 0 < value
  deriving DecidableEq

namespace PositiveArity

/-- The smallest positive arity. -/
def one : PositiveArity := ⟨1, by decide⟩

@[simp] theorem one_value : one.value = 1 := rfl

end PositiveArity

/-- The Euclidean configuration space of `n` ordered points in spacetime dimension `d`. -/
abbrev EuclideanNPointSpace (d : EuclideanDimension) (n : ℕ) :=
  Fin n → d.Spacetime

/-- Complex scalar Schwartz test functions on the `n`-point Euclidean configuration space. -/
abbrev ScalarSchwartzTestFunction (d : EuclideanDimension) (n : ℕ) :=
  SchwartzMap (EuclideanNPointSpace d n) ℂ

/-- A complex scalar tempered distribution on the `n`-point Euclidean configuration space. -/
abbrev ScalarTemperedSchwingerDistribution (d : EuclideanDimension) (n : ℕ) :=
  TemperedDistribution (EuclideanNPointSpace d n) ℂ

/-- A normalized scalar family of positive-arity tempered Schwinger distributions.

The zero-point value is separate because `(E0′)` fixes `S₀ = 1`, whereas positive arities are
continuous linear functionals on nonzero-arity Schwartz spaces. This record carries no OS axiom
other than ordinary tempered-distribution regularity and zero-point normalization. -/
structure ScalarSchwingerDistributionFamily (d : EuclideanDimension) where
  /-- The scalar zero-point function. -/
  zeroPoint : ℂ
  /-- The source normalization `S₀ = 1`. -/
  zeroPoint_normalized : zeroPoint = 1
  /-- The tempered distribution at each actual positive arity. -/
  positivePoint : ∀ n : PositiveArity,
    ScalarTemperedSchwingerDistribution d n.value

/-- Positive coefficients with one uniform factorial-growth estimate.

This packages the phrase “a sequence of positive numbers of factorial growth” from OS-II printed
p. 287. The exponent is a nonnegative real and `Real.rpow` records the source's real-power bound
without silently rounding it to a natural exponent. -/
structure FactorialGrowthSequence where
  /-- The coefficient indexed by the actual positive arity. -/
  coefficient : PositiveArity → ℝ
  /-- OS-II requires positive coefficients. -/
  coefficient_pos : ∀ n, 0 < coefficient n
  /-- The uniform multiplicative constant. -/
  amplitude : ℝ
  /-- The multiplicative constant is positive. -/
  amplitude_pos : 0 < amplitude
  /-- The uniform factorial exponent. -/
  exponent : ℝ
  /-- Negative factorial powers are not accepted as the growth convention. -/
  exponent_nonneg : 0 ≤ exponent
  /-- Every coefficient is bounded by one fixed power of the factorial of its actual arity. -/
  factorial_bound : ∀ n,
    coefficient n ≤ amplitude * Real.rpow (n.value.factorial : ℝ) exponent

/-- A concrete fixed-order control built from Mathlib's Schwartz seminorm family.

For one order `s`, this sums all weighted Fréchet-derivative seminorms with weight and derivative
orders at most `s`. It is an explicit nonnegative control on the full Schwartz space. No equivalence
with the precise OS-I printed norm is asserted here. -/
noncomputable def mathlibSchwartzOrderControl
    (d : EuclideanDimension) (n s : ℕ) (f : ScalarSchwartzTestFunction d n) : ℝ :=
  ∑ k ∈ Finset.range (s + 1),
    ∑ m ∈ Finset.range (s + 1), SchwartzMap.seminorm ℂ k m f

/-- The concrete fixed-order Schwartz control is nonnegative. -/
theorem mathlibSchwartzOrderControl_nonnegative
    (d : EuclideanDimension) (n s : ℕ) (f : ScalarSchwartzTestFunction d n) :
    0 ≤ mathlibSchwartzOrderControl d n s f := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro m _
  positivity

/-- The concrete fixed-order control separates Schwartz test functions. -/
theorem mathlibSchwartzOrderControl_eq_zero_iff
    (d : EuclideanDimension) (n s : ℕ) (f : ScalarSchwartzTestFunction d n) :
    mathlibSchwartzOrderControl d n s f = 0 ↔ f = 0 := by
  constructor
  · intro hcontrol
    unfold mathlibSchwartzOrderControl at hcontrol
    have houterNonneg : ∀ k ∈ Finset.range (s + 1),
        0 ≤ ∑ m ∈ Finset.range (s + 1), SchwartzMap.seminorm ℂ k m f := by
      intro k _
      apply Finset.sum_nonneg
      intro m _
      positivity
    have houter :=
      (Finset.sum_eq_zero_iff_of_nonneg houterNonneg).mp hcontrol
    have hinnerZero := houter 0 (by simp)
    have hinnerNonneg : ∀ m ∈ Finset.range (s + 1),
        0 ≤ SchwartzMap.seminorm ℂ 0 m f := by
      intro m _
      positivity
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg hinnerNonneg).mp hinnerZero
    have hseminorm : SchwartzMap.seminorm ℂ 0 0 f = 0 :=
      hterms 0 (by simp)
    ext x
    have hx := SchwartzMap.norm_le_seminorm ℂ f x
    rw [hseminorm] at hx
    exact norm_eq_zero.mp (le_antisymm hx (norm_nonneg _))
  · rintro rfl
    simp [mathlibSchwartzOrderControl]

/-- One fixed positive Schwartz order and one factorial-growth sequence control every positive
arity.

This is a named Mathlib-convention strengthening candidate, not yet the source-facing OS-II
`(E0′)` record. The future comparison theorem must account for test-space and seminorm conventions
before this data can feed a reconstruction bridge. -/
structure MathlibFixedOrderFactorialGrowthData
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) where
  /-- The single Schwartz order used at every arity. -/
  order : ℕ
  /-- OS-II chooses a positive fixed order. -/
  order_positive : 0 < order
  /-- The uniform factorial-growth coefficient sequence. -/
  growth : FactorialGrowthSequence
  /-- The positive-point distributions satisfy the fixed-order estimate at their exact arity. -/
  bound : ∀ (n : PositiveArity) (f : ScalarSchwartzTestFunction d n.value),
    ‖family.positivePoint n f‖ ≤
      growth.coefficient n * mathlibSchwartzOrderControl d n.value order f

end YangMills
