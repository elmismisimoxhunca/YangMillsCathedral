/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteSequence
import YangMills.Euclidean.SchwingerExtendedSequenceProbes

/-!
# Hostile probes for unrestricted finite Schwartz sequences

The probes ensure forgetting positive-time structure preserves exact components/support and that the
unrestricted carrier still rejects disconnected finite supports.
-/

namespace YangMills.Euclidean.SchwingerFiniteSequence.Probes

/-- Support membership remains exactly component nonvanishing. -/
theorem exact_unrestricted_support
    {d : EuclideanDimension} (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    n ∈ f.support ↔ f.component n ≠ 0 :=
  f.mem_support_iff n

/-- A nonzero component outside exact unrestricted support is rejected. -/
theorem nonzero_outside_unrestricted_support_blocked
    {d : EuclideanDimension} (f : ScalarFiniteSchwartzSequence d) (n : ℕ)
    (hn : n ∉ f.support) (hnonzero : f.component n ≠ 0) : False :=
  hnonzero (f.component_eq_zero_of_not_mem n hn)

/-- The unrestricted zero sequence has empty support. -/
@[simp] theorem zero_unrestricted_support (d : EuclideanDimension) :
    (zeroScalarFiniteSchwartzSequence d).support = ∅ :=
  rfl

/-- The unrestricted scalar unit is supported exactly at arity zero. -/
@[simp] theorem scalar_unit_unrestricted_support (d : EuclideanDimension) :
    (scalarUnitFiniteSchwartzSequence d).support = {0} := by
  exact _root_.YangMills.Euclidean.SchwingerExtendedSequence.Probes.unitZeroPoint_sequence_naturalSupport d

/-- Forgetting strict positive-time evidence from the singleton bump preserves support `{1}`. -/
@[simp] theorem forgotten_singleton_bump_support (d : EuclideanDimension) :
    ((singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support = {1} := by
  exact _root_.YangMills.Euclidean.SchwingerExtendedSequence.Probes.singleton_bump_sequence_naturalSupport d

/-- Forgetting strict positive-time evidence preserves the exact nonzero bump component. -/
theorem forgotten_singleton_bump_component
    (d : EuclideanDimension) :
    ((singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).component 1 =
      positiveTimeBumpSchwartz d :=
  _root_.YangMills.Euclidean.SchwingerExtendedSequence.Probes.singleton_extendedComponent_one d

/-- Omitting the retained nonzero bump from unrestricted support is impossible. -/
theorem omitted_forgotten_bump_support_blocked
    (d : EuclideanDimension)
    (homitted : 1 ∉ ((singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support) :
    False :=
  homitted (by
    rw [MathlibStrictPositiveTimeTestSequence.toFiniteSchwartzSequence_support]
    have hsupport := _root_.YangMills.Euclidean.SchwingerExtendedSequence.Probes.singleton_bump_sequence_naturalSupport d
    rw [hsupport]
    simp)

end YangMills.Euclidean.SchwingerFiniteSequence.Probes
