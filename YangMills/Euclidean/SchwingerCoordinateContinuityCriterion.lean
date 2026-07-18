/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerCoordinateInjection

/-!
# Linear coordinate continuity criterion for finite Schwinger sequences

OS-I, printed p. 87, characterizes its direct-sum topology by continuity of a linear map after every
natural coordinate injection. For the project's preliminary finite-stage final topology, this module
proves the exact analogous theorem.

The proof first decomposes every finite stage into the finite sum of its exact coordinate
injections. Therefore a linear map out is continuous on every finite stage whenever all coordinate
composites are continuous; the previously proved finite-stage universal property then gives global
continuity.

This theorem concerns the current full Mathlib Schwartz spaces and preliminary final topology. It
does not identify them with OS-I's diagonal-sensitive source spaces or printed locally convex direct
sum, and it does not prove joint continuity of the sequence algebra operations.
-/

namespace YangMills

noncomputable local instance scalarFiniteSchwartzCriterionTopologyLocal
    (d : EuclideanDimension) : TopologicalSpace (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzFiniteStageFinalTopology d

noncomputable local instance scalarFiniteSchwartzCriterionAddCommGroupLocal
    (d : EuclideanDimension) : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceAddCommGroup d

noncomputable local instance scalarFiniteSchwartzCriterionModuleLocal
    (d : EuclideanDimension) : Module ℂ (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceModule d

/-- Taking one exact component commutes with a finite sum in the named pointwise sequence module. -/
theorem scalarFiniteSchwartzSequence_finset_sum_component
    (d : EuclideanDimension) {α : Type*} [DecidableEq α]
    (u : Finset α) (F : α → ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (∑ a ∈ u, F a).component n = ∑ a ∈ u, (F a).component n := by
  induction u using Finset.induction_on with
  | empty => rfl
  | @insert a u ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (addScalarFiniteSchwartzSequence d (F a) (∑ x ∈ u, F x)).component n = _
      rw [addScalarFiniteSchwartzSequence_component, ih]

/-- An exact finite-stage sequence is the finite sum of its natural coordinate injections. -/
theorem scalarFiniteSchwartzStage_coordinate_decomposition
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s) :
    scalarFiniteSchwartzStageToSequence d s x =
      ∑ q : {n // n ∈ s},
        scalarSchwartzCoordinateInjectionContinuousLinearMap d q.val (x q) := by
  apply ScalarFiniteSchwartzSequence.ext
  intro m
  rw [scalarFiniteSchwartzStageToSequence_component,
    scalarFiniteSchwartzSequence_finset_sum_component]
  by_cases hm : m ∈ s
  · let q0 : {n // n ∈ s} := ⟨m, hm⟩
    rw [Finset.sum_eq_single q0]
    · rw [scalarSchwartzCoordinateInjection_component_self]
      exact scalarFiniteSchwartzStageComponent_of_mem d s x m hm
    · intro q _ hq
      rw [scalarSchwartzCoordinateInjection_component_ne]
      intro heq
      apply hq
      exact Subtype.ext heq.symm
    · simp
  · rw [scalarFiniteSchwartzStageComponent_of_not_mem d s x m hm]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [scalarSchwartzCoordinateInjection_component_ne]
    intro heq
    apply hm
    rw [heq]
    exact q.property

/-- Exact linear coordinate-injection criterion for the preliminary finite-stage final topology.

A complex-linear map into any topological complex module with continuous addition is continuous iff
its composite with every exact natural coordinate injection is continuous. -/
theorem continuous_linearMap_from_scalarFiniteSchwartzSequence_iff_coordinates
    (d : EuclideanDimension) {Y : Type*}
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [ContinuousAdd Y]
    (L : ScalarFiniteSchwartzSequence d →ₗ[ℂ] Y) :
    Continuous L ↔
      ∀ n : ℕ, Continuous (fun f : ScalarSchwartzTestFunction d n =>
        L (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f)) := by
  constructor
  · intro h n
    exact h.comp (scalarSchwartzCoordinateInjectionContinuousLinearMap d n).continuous
  · intro h
    rw [continuous_from_scalarFiniteSchwartzFiniteStageFinalTopology_iff]
    intro s
    have heq : (L ∘ scalarFiniteSchwartzStageToSequence d s) =
        fun x => ∑ q : {n // n ∈ s},
          L (scalarSchwartzCoordinateInjectionContinuousLinearMap d q.val (x q)) := by
      funext x
      rw [Function.comp_apply, scalarFiniteSchwartzStage_coordinate_decomposition, map_sum]
    rw [heq]
    apply continuous_finsetSum Finset.univ
    intro q _
    exact (h q.val).comp (continuous_apply q)

end YangMills
