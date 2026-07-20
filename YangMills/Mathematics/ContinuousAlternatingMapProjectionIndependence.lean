/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Projection independence of horizontal alternating maps

A finite-arity continuous alternating map that vanishes whenever one argument lies in the kernel of
a linear projection depends only on the projected tuple. The arbitrary-degree proof uses Mathlib's
finite multilinear telescoping identity and includes arity zero.
-/

namespace YangMills.Mathematics

universe uR uE uF uV

variable
    {R : Type uR} [Ring R]
    {E : Type uE} [AddCommGroup E] [Module R E] [TopologicalSpace E]
    {F : Type uF} [AddCommGroup F] [Module R F]
    {V : Type uV} [AddCommGroup V] [Module R V] [TopologicalSpace V]

/-- Replacing one argument by one with the same projection leaves a horizontal continuous
alternating map unchanged. -/
theorem _root_.ContinuousAlternatingMap.eq_update_of_sub_mem_ker {k : ℕ}
    (form : ContinuousAlternatingMap R E V (Fin k))
    (projection : E →ₗ[R] F)
    (horizontal : ∀ v : Fin k → E,
      (∃ i, projection (v i) = 0) → form v = 0)
    (args : Fin k → E) (i : Fin k) (replacement : E)
    (verticalDifference : projection (args i - replacement) = 0) :
    form args = form (Function.update args i replacement) := by
  have zeroInsertion : form (Function.update args i (args i - replacement)) = 0 := by
    apply horizontal
    refine ⟨i, ?_⟩
    simpa using verticalDifference
  rw [form.map_update_sub] at zeroInsertion
  exact sub_eq_zero.mp (by simpa using zeroInsertion)

/-- A horizontal continuous alternating map takes equal values on tuples with coordinatewise equal
projections, in every finite arity. -/
theorem _root_.ContinuousAlternatingMap.eq_of_linearMap_apply_eq {k : ℕ}
    (form : ContinuousAlternatingMap R E V (Fin k))
    (projection : E →ₗ[R] F)
    (horizontal : ∀ v : Fin k → E,
      (∃ i, projection (v i) = 0) → form v = 0)
    (first second : Fin k → E)
    (sameProjection : ∀ i, projection (first i) = projection (second i)) :
    form first = form second := by
  classical
  have telescope := form.toMultilinearMap.map_sub_map_piecewise
    first second (Finset.univ : Finset (Fin k))
  have right_eq : (Finset.univ : Finset (Fin k)).piecewise second first = second := by
    funext i
    simp
  rw [right_eq] at telescope
  have summand_zero : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      form.toMultilinearMap
        (fun j ↦ if j ∈ (Finset.univ : Finset (Fin k)) → j < i then first j
          else if i = j then first j - second j else second j) = 0 := by
    intro i _
    change form
      (fun j ↦ if j ∈ (Finset.univ : Finset (Fin k)) → j < i then first j
        else if i = j then first j - second j else second j) = 0
    apply horizontal
    refine ⟨i, ?_⟩
    simp only [Finset.mem_univ, true_implies, lt_self_iff_false, ↓reduceIte]
    rw [map_sub, sameProjection i, sub_self]
  rw [Finset.sum_eq_zero summand_zero] at telescope
  change form first - form second = 0 at telescope
  exact sub_eq_zero.mp telescope

end YangMills.Mathematics
