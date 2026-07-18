/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerExtendedSequence

/-!
# Unrestricted finite scalar Schwartz sequences

Osterwalder–Schrader I distinguishes the unrestricted finite test-sequence algebra `_𝒮` from its
positive-time subspace `_𝒮₊`. Products of positive-time sequences need not remain globally
positive-time ordered, so the convolution output must not be forced back into the project's strict
positive-time carrier.

This module defines the unrestricted algebraic carrier: one exact Schwartz test at every natural
arity and a finset exactly equal to its nonzero support. It also forgets the ordered/flat evidence
from a strict positive-time sequence without changing any component. No topology or product is
installed here.
-/

namespace YangMills

/-- An unrestricted finite scalar Schwartz sequence indexed by all natural arities. -/
structure ScalarFiniteSchwartzSequence (d : EuclideanDimension) where
  /-- The exact finite set of nonzero natural arities. -/
  support : Finset ℕ
  /-- The bundled scalar Schwartz component at every natural arity. -/
  component : (n : ℕ) → ScalarSchwartzTestFunction d n
  /-- Support membership is exactly nonvanishing of the same dependent component. -/
  mem_support_iff : ∀ n, n ∈ support ↔ component n ≠ 0

namespace ScalarFiniteSchwartzSequence

/-- Every component outside exact support vanishes. -/
theorem component_eq_zero_of_not_mem
    {d : EuclideanDimension} (f : ScalarFiniteSchwartzSequence d)
    (n : ℕ) (hn : n ∉ f.support) : f.component n = 0 := by
  by_contra hnonzero
  exact hn ((f.mem_support_iff n).2 hnonzero)

/-- Every nonzero component belongs to exact support. -/
theorem mem_support_of_component_ne_zero
    {d : EuclideanDimension} (f : ScalarFiniteSchwartzSequence d)
    (n : ℕ) (hn : f.component n ≠ 0) : n ∈ f.support :=
  (f.mem_support_iff n).2 hn

end ScalarFiniteSchwartzSequence

/-- The unrestricted sequence with every component zero. -/
noncomputable def zeroScalarFiniteSchwartzSequence (d : EuclideanDimension) :
    ScalarFiniteSchwartzSequence d where
  support := ∅
  component := fun _ => 0
  mem_support_iff := by simp

/-- Forget positive-time ordered/flat evidence while preserving every exact natural-arity component
and exact support. -/
noncomputable def MathlibStrictPositiveTimeTestSequence.toFiniteSchwartzSequence
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) :
    ScalarFiniteSchwartzSequence d where
  support := f.naturalSupport
  component := f.extendedComponent
  mem_support_iff := f.mem_naturalSupport_iff

/-- Forgetting positive-time structure preserves the exact component at every natural arity. -/
@[simp] theorem MathlibStrictPositiveTimeTestSequence.toFiniteSchwartzSequence_component
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) (n : ℕ) :
    f.toFiniteSchwartzSequence.component n = f.extendedComponent n :=
  rfl

/-- Forgetting positive-time structure preserves exact natural support. -/
@[simp] theorem MathlibStrictPositiveTimeTestSequence.toFiniteSchwartzSequence_support
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) :
    f.toFiniteSchwartzSequence.support = f.naturalSupport :=
  rfl

/-- The unrestricted scalar unit sequence, supported exactly at arity zero. -/
noncomputable def scalarUnitFiniteSchwartzSequence (d : EuclideanDimension) :
    ScalarFiniteSchwartzSequence d :=
  (unitZeroPointTestSequence d).toFiniteSchwartzSequence

end YangMills
