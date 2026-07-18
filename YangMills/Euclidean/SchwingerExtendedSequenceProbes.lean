/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerExtendedSequence

/-!
# Hostile probes for natural-arity sequence extension

These probes ensure arity zero is represented faithfully, natural support is exact, and neither the
zero-point scalar nor positive components can be omitted from future convolution sums.
-/

namespace YangMills.Euclidean.SchwingerExtendedSequence.Probes

/-- Natural support is exactly nonvanishing of the same extended component. -/
theorem exact_natural_support
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) (n : ℕ) :
    n ∈ f.naturalSupport ↔ f.extendedComponent n ≠ 0 :=
  f.mem_naturalSupport_iff n

/-- The all-zero sequence has empty natural support. -/
@[simp] theorem zero_sequence_naturalSupport
    (d : EuclideanDimension) :
    (zeroStrictPositiveTimeTestSequence d).naturalSupport = ∅ := by
  simp [MathlibStrictPositiveTimeTestSequence.naturalSupport,
    zeroStrictPositiveTimeTestSequence]

/-- The scalar-unit sequence has exactly arity zero in natural support. -/
@[simp] theorem unitZeroPoint_sequence_naturalSupport
    (d : EuclideanDimension) :
    (unitZeroPointTestSequence d).naturalSupport = {0} := by
  simp [MathlibStrictPositiveTimeTestSequence.naturalSupport,
    unitZeroPointTestSequence]

/-- The singleton positive-time bump sequence has exactly natural arity one in support. -/
@[simp] theorem singleton_bump_sequence_naturalSupport
    (d : EuclideanDimension) :
    (singletonPositiveTimeBumpSequence d).naturalSupport = {1} := by
  simp [MathlibStrictPositiveTimeTestSequence.naturalSupport,
    singletonPositiveTimeBumpSequence]

/-- The extended arity-zero unit component evaluates exactly to one. -/
theorem unitZeroPoint_extendedComponent_apply
    (d : EuclideanDimension) (x : EuclideanNPointSpace d 0) :
    (unitZeroPointTestSequence d).extendedComponent 0 x = 1 := by
  simp [unitZeroPointTestSequence]

/-- The extended arity-one singleton component is the exact nonzero bump. -/
theorem singleton_extendedComponent_one
    (d : EuclideanDimension) :
    (singletonPositiveTimeBumpSequence d).extendedComponent 1 =
      positiveTimeBumpSchwartz d := by
  rw [MathlibStrictPositiveTimeTestSequence.extendedComponent_succ]
  exact singletonPositiveTimeBumpSequence_component_one d

/-- Omitting a nonzero extended component from natural support is rejected. -/
theorem omitted_natural_support_blocked
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) (n : ℕ)
    (hnonzero : f.extendedComponent n ≠ 0) (homitted : n ∉ f.naturalSupport) : False :=
  homitted ((f.mem_naturalSupport_iff n).2 hnonzero)

/-- Replacing two distinct scalars by the same zero-arity Schwartz function is impossible. -/
theorem zeroArity_scalar_replacement_blocked
    (d : EuclideanDimension) (a b : ℂ) (hne : a ≠ b)
    (heq : scalarZeroAritySchwartz d a = scalarZeroAritySchwartz d b) : False :=
  hne (scalarZeroAritySchwartz_injective d heq)

end YangMills.Euclidean.SchwingerExtendedSequence.Probes
