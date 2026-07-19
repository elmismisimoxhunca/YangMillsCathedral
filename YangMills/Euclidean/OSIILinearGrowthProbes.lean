/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSIILinearGrowth

/-!
# Hostile probes for the OS-II ambient-extension linear-growth strengthening

These probes lock the exact flattened-coordinate weight, multi-index terms, least-upper-bound
characterization, coincidence-flat equation (4.1), one common positive order, and factorial
coefficients. They construct no control, Schwinger family, or reconstruction.
-/

namespace YangMills.OSIILinearGrowth.Probes

open YangMills

/-- The configuration square is the sum over all point and coordinate labels, not the outer
function-space supremum norm. -/
example {n : ℕ} (x : EuclideanNPointSpace EuclideanDimension.four n) :
    fourDimensionalConfigurationSquaredNorm x = ∑ i, ∑ μ, (x i μ) ^ 2 :=
  rfl

/-- The raw term uses the printed `(1 + x²)^(p/2)` weight and exact `D^α`. -/
example {n : ℕ} (p : ℕ) (α : FourDimensionalMultiIndex n)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    osIIPrintedWeightedDerivativeTerm p α f x =
      Real.rpow (1 + fourDimensionalConfigurationSquaredNorm x) ((p : ℝ) / 2) *
        ‖fourDimensionalMultiIndexDerivative α f x‖ :=
  rfl

/-- Every exact displayed term below the common order is controlled. -/
example {n p : ℕ} (data : OSIIPrintedSchwartzControlData n p)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n) (hα : fourDimensionalMultiIndexOrder α ≤ p)
    (x : EuclideanNPointSpace EuclideanDimension.four n) :
    osIIPrintedWeightedDerivativeTerm p α f x ≤ data.control f :=
  data.weightedDerivative_le f α hα x

/-- An unrelated larger upper bound does not redefine the exact control: leastness remains visible. -/
example {n p : ℕ} (data : OSIIPrintedSchwartzControlData n p)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n) (bound : ℝ)
    (upper : ∀ (α : FourDimensionalMultiIndex n),
      fourDimensionalMultiIndexOrder α ≤ p → ∀ x,
        osIIPrintedWeightedDerivativeTerm p α f x ≤ bound) :
    data.control f ≤ bound :=
  data.control_le_of_weightedDerivative_le f bound upper

/-- Two supplied controls with the exact universal property cannot disagree. -/
example {n p : ℕ} (first second : OSIIPrintedSchwartzControlData n p) :
    first.control = second.control :=
  first.control_unique second

/-- A strictly positive displayed term blocks the fake zero control. -/
example {n p : ℕ} (data : OSIIPrintedSchwartzControlData n p)
    (f : ScalarSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n) (hα : fourDimensionalMultiIndexOrder α ≤ p)
    (x : EuclideanNPointSpace EuclideanDimension.four n)
    (positive : 0 < osIIPrintedWeightedDerivativeTerm p α f x) :
    data.control f ≠ 0 :=
  data.control_ne_zero_of_term_pos f α hα x positive

variable
    {family : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    (growth : OSIIAmbientExtensionLinearGrowthData family)

/-- OS-II uses one positive order at every arity. -/
example : 0 < growth.order :=
  growth.order_positive

/-- Every exact coefficient is positive; a zero-growth sequence is rejected. -/
example (n : PositiveArity) : 0 < growth.growth.coefficient n :=
  growth.growth.coefficient_pos n

/-- Equation (4.1) uses the exact same family, coefficient, order, and printed control. -/
example (n : PositiveArity)
    (f : OSIICoincidenceFlatSchwartzTestFunction n.value) :
    ‖family.positivePoint n f.1‖ ≤
      growth.growth.coefficient n * (growth.printedControl n).control f.1 :=
  growth.bound n f

end YangMills.OSIILinearGrowth.Probes
