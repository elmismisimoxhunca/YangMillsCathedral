/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerOrderedTestSpace

/-!
# Finite scalar Schwinger test sequences

Osterwalder–Schrader I, printed pp. 87–88, forms finite sequences
`f = {f₀, f₁, …}` with `f₀ ∈ ℂ`, one positive-time test at each positive arity, and all but finitely
many components zero. This module packages the algebraic finite-support data over the project's
strict Mathlib ordered subspace. It does not install OS-I's direct-sum topology and does not define
the sequence product, involution, or reflection positivity `(E2)`.

The support finset is required to equal, not merely contain, the nonzero positive arities. This keeps
later double sums connected to the actual components and prevents arbitrary finite index witnesses.
-/

namespace YangMills

/-- A finite scalar positive-time test sequence over the strict Mathlib ordered subspace. -/
structure MathlibStrictPositiveTimeTestSequence (d : EuclideanDimension) where
  /-- The arity-zero scalar component. -/
  zeroPoint : ℂ
  /-- The exact finite set of nonzero positive arities. -/
  support : Finset PositiveArity
  /-- The underlying Schwartz test at every positive arity. -/
  component : ∀ n : PositiveArity, ScalarSchwartzTestFunction d n.value
  /-- Every component has strict positive-time ordered topological support. -/
  component_ordered : ∀ n, HasStrictPositiveTimeOrderedSupport d (component n)
  /-- Every component is infinitely Fréchet-flat on point coincidences. -/
  component_flat : ∀ n, IsFlatAtPointCoincidences (component n)
  /-- The finset is exactly the nonzero support, not a disconnected finite superset. -/
  mem_support_iff : ∀ n, n ∈ support ↔ component n ≠ 0

namespace MathlibStrictPositiveTimeTestSequence

/-- A component outside the exact support is zero. -/
theorem component_eq_zero_of_not_mem
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d)
    (n : PositiveArity) (hn : n ∉ f.support) : f.component n = 0 := by
  by_contra hnonzero
  exact hn ((f.mem_support_iff n).2 hnonzero)

/-- A nonzero component belongs to the exact support. -/
theorem mem_support_of_component_ne_zero
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d)
    (n : PositiveArity) (hn : f.component n ≠ 0) : n ∈ f.support :=
  (f.mem_support_iff n).2 hn

end MathlibStrictPositiveTimeTestSequence

/-- The zero Schwartz component has strict ordered support vacuously. -/
theorem zero_hasStrictPositiveTimeOrderedSupport
    (d : EuclideanDimension) (n : ℕ) :
    HasStrictPositiveTimeOrderedSupport d (0 : ScalarSchwartzTestFunction d n) := by
  change tsupport (0 : EuclideanNPointSpace d n → ℂ) ⊆ _
  rw [tsupport_zero]
  exact Set.empty_subset _

/-- The zero Schwartz component is infinitely flat at coincidences. -/
theorem zero_isFlatAtPointCoincidences
    (d : EuclideanDimension) (n : ℕ) :
    IsFlatAtPointCoincidences (0 : ScalarSchwartzTestFunction d n) := by
  intro k x _
  change iteratedFDeriv ℝ k (0 : EuclideanNPointSpace d n → ℂ) x = 0
  rw [iteratedFDeriv_zero]
  rfl

/-- The finite sequence with every component zero. -/
noncomputable def zeroStrictPositiveTimeTestSequence (d : EuclideanDimension) :
    MathlibStrictPositiveTimeTestSequence d where
  zeroPoint := 0
  support := ∅
  component := fun _ => 0
  component_ordered := fun n => zero_hasStrictPositiveTimeOrderedSupport d n.value
  component_flat := fun n => zero_isFlatAtPointCoincidences d n.value
  mem_support_iff := by simp

/-- The arity-one bump component, zero at every other positive arity. -/
noncomputable def singletonPositiveTimeBumpComponent
    (d : EuclideanDimension) (n : PositiveArity) :
    ScalarSchwartzTestFunction d n.value := by
  by_cases h : n = PositiveArity.one
  · subst n
    exact positiveTimeBumpSchwartz d
  · exact 0

/-- A finite sequence whose sole nonzero positive component is the explicit arity-one positive-time
bump and whose zero-point component is zero. -/
noncomputable def singletonPositiveTimeBumpSequence (d : EuclideanDimension) :
    MathlibStrictPositiveTimeTestSequence d where
  zeroPoint := 0
  support := {PositiveArity.one}
  component := singletonPositiveTimeBumpComponent d
  component_ordered := by
    intro n
    by_cases h : n = PositiveArity.one
    · subst n
      exact (positiveTimeBumpOrderedFlatTest d).ordered_support
    · simp only [singletonPositiveTimeBumpComponent, h, dite_false]
      exact zero_hasStrictPositiveTimeOrderedSupport d n.value
  component_flat := by
    intro n
    by_cases h : n = PositiveArity.one
    · subst n
      exact (positiveTimeBumpOrderedFlatTest d).coincidence_flat
    · simp only [singletonPositiveTimeBumpComponent, h, dite_false]
      exact zero_isFlatAtPointCoincidences d n.value
  mem_support_iff := by
    intro n
    by_cases h : n = PositiveArity.one
    · subst n
      simp [singletonPositiveTimeBumpComponent]
      exact positiveTimeBumpSchwartz_ne_zero d
    · simp [singletonPositiveTimeBumpComponent, h]

/-- The singleton sequence's arity-one component is definitionally connected to the explicit bump. -/
theorem singletonPositiveTimeBumpSequence_component_one
    (d : EuclideanDimension) :
    (singletonPositiveTimeBumpSequence d).component PositiveArity.one =
      positiveTimeBumpSchwartz d := by
  simp [singletonPositiveTimeBumpSequence, singletonPositiveTimeBumpComponent]

end YangMills
