/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerRegularity

/-!
# Hostile probes for scalar Schwinger regularity

These probes reject empty arity indexing, malformed zero-point normalization, nonpositive growth
coefficients, negative factorial exponents, and disconnected fixed-order bounds. They do not
construct an OS theory or a Yang–Mills model.
-/

namespace YangMills.Euclidean.SchwingerRegularity.Probes

/-- The positive-arity index is inhabited, so universal positive-point fields are not vacuous. -/
theorem positive_arity_is_nonempty : Nonempty PositiveArity :=
  ⟨PositiveArity.one⟩

/-- No positive-arity index can silently carry arity zero. -/
theorem zero_arity_blocked (n : PositiveArity) (hzero : n.value = 0) : False :=
  (Nat.ne_of_gt n.positive) hzero

/-- A normalized scalar Schwinger family cannot replace `S₀ = 1` by zero. -/
theorem zero_point_cannot_vanish
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (hzero : family.zeroPoint = 0) : False := by
  rw [family.zeroPoint_normalized] at hzero
  norm_num at hzero

/-- A purported nonpositive factorial-growth coefficient contradicts the source-facing positivity
field at that exact arity. -/
theorem nonpositive_growth_coefficient_blocked
    (growth : FactorialGrowthSequence) (n : PositiveArity)
    (hnonpositive : growth.coefficient n ≤ 0) : False :=
  (not_lt_of_ge hnonpositive) (growth.coefficient_pos n)

/-- A nonpositive amplitude cannot inhabit the factorial-growth convention. -/
theorem nonpositive_growth_amplitude_blocked
    (growth : FactorialGrowthSequence) (hnonpositive : growth.amplitude ≤ 0) : False :=
  (not_lt_of_ge hnonpositive) growth.amplitude_pos

/-- A negative factorial exponent cannot inhabit the declared growth convention. -/
theorem negative_factorial_exponent_blocked
    (growth : FactorialGrowthSequence) (hnegative : growth.exponent < 0) : False :=
  (not_lt_of_ge growth.exponent_nonneg) hnegative

/-- The projected factorial estimate uses the factorial of the exact positive arity and the same
amplitude and real exponent carried by the growth record. -/
theorem exact_factorial_growth_bound
    (growth : FactorialGrowthSequence) (n : PositiveArity) :
    growth.coefficient n ≤
      growth.amplitude * Real.rpow (n.value.factorial : ℝ) growth.exponent :=
  growth.factorial_bound n

/-- The fixed-order record cannot use order zero. -/
theorem zero_schwartz_order_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (data : MathlibFixedOrderFactorialGrowthData family) (hzero : data.order = 0) : False :=
  (Nat.ne_of_gt data.order_positive) hzero

/-- The fixed-order control vanishes on the zero test function. -/
@[simp] theorem mathlib_control_zero
    (d : EuclideanDimension) (n s : ℕ) :
    mathlibSchwartzOrderControl d n s (0 : ScalarSchwartzTestFunction d n) = 0 := by
  simp [mathlibSchwartzOrderControl]

/-- Zero designated control forces the test function itself to vanish, so the control cannot be
replaced by an identically-zero implementation. -/
theorem zero_control_forces_zero_test_function
    (d : EuclideanDimension) (n s : ℕ) (f : ScalarSchwartzTestFunction d n)
    (hcontrol : mathlibSchwartzOrderControl d n s f = 0) : f = 0 :=
  (mathlibSchwartzOrderControl_eq_zero_iff d n s f).mp hcontrol

/-- The regularity record controls the same family, test function, and actual positive arity shown
in its conclusion; no unrelated distribution can discharge this projection. -/
theorem exact_arity_bound
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (data : MathlibFixedOrderFactorialGrowthData family)
    (n : PositiveArity) (f : ScalarSchwartzTestFunction d n.value) :
    ‖family.positivePoint n f‖ ≤
      data.growth.coefficient n *
        mathlibSchwartzOrderControl d n.value data.order f :=
  data.bound n f

/-- If the designated control vanishes, the exact controlled distribution must vanish on that test
function. This blocks a disconnected bound from controlling an unrelated family or arity. -/
theorem uncontrolled_nonzero_value_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (data : MathlibFixedOrderFactorialGrowthData family)
    (n : PositiveArity) (f : ScalarSchwartzTestFunction d n.value)
    (hcontrol : mathlibSchwartzOrderControl d n.value data.order f = 0)
    (hvalue : family.positivePoint n f ≠ 0) : False := by
  have hbound := data.bound n f
  rw [hcontrol, mul_zero] at hbound
  have hnorm : ‖family.positivePoint n f‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  exact hvalue (norm_eq_zero.mp hnorm)

end YangMills.Euclidean.SchwingerRegularity.Probes
