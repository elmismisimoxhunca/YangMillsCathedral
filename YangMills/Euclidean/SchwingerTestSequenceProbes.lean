/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTestSequence

/-!
# Hostile probes for finite Schwinger test sequences

These probes ensure finite support is exact, components outside it vanish, and the explicit
singleton sequence remains connected to the nonzero positive-time bump. They do not define the
sequence product or reflection positivity.
-/

namespace YangMills.Euclidean.SchwingerTestSequence.Probes

/-- Membership in the sequence support is exactly nonvanishing of that same component. -/
theorem exact_support_characterization
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d)
    (n : PositiveArity) :
    n ∈ f.support ↔ f.component n ≠ 0 :=
  f.mem_support_iff n

/-- A purported nonzero component outside the exact support is rejected. -/
theorem nonzero_component_outside_support_blocked
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d)
    (n : PositiveArity) (hn : n ∉ f.support) (hnonzero : f.component n ≠ 0) : False :=
  hnonzero (f.component_eq_zero_of_not_mem n hn)

/-- The zero sequence has no positive support. -/
@[simp] theorem zero_sequence_support
    (d : EuclideanDimension) :
    (zeroStrictPositiveTimeTestSequence d).support = ∅ :=
  rfl

/-- Arity one belongs to the exact singleton-bump support. -/
@[simp] theorem one_mem_singleton_bump_support
    (d : EuclideanDimension) :
    PositiveArity.one ∈ (singletonPositiveTimeBumpSequence d).support := by
  simp [singletonPositiveTimeBumpSequence]

/-- The singleton sequence's supported component is the exact explicit bump. -/
theorem singleton_bump_component_exact
    (d : EuclideanDimension) :
    (singletonPositiveTimeBumpSequence d).component PositiveArity.one =
      positiveTimeBumpSchwartz d :=
  singletonPositiveTimeBumpSequence_component_one d

/-- The sole supported positive component is genuinely nonzero. -/
theorem singleton_bump_component_nonzero
    (d : EuclideanDimension) :
    (singletonPositiveTimeBumpSequence d).component PositiveArity.one ≠ 0 := by
  rw [singletonPositiveTimeBumpSequence_component_one]
  exact positiveTimeBumpSchwartz_ne_zero d

/-- Replacing the exact support by one that omits the nonzero arity-one component contradicts the
support characterization. -/
theorem omitted_singleton_support_blocked
    (d : EuclideanDimension)
    (homitted : PositiveArity.one ∉ (singletonPositiveTimeBumpSequence d).support) : False :=
  homitted (one_mem_singleton_bump_support d)

end YangMills.Euclidean.SchwingerTestSequence.Probes
