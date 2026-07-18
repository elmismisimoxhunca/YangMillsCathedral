/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteStageContinuousLinear
import YangMills.Euclidean.SchwingerConvolutionComponent

/-!
# Continuous linear coordinate injections into finite Schwinger sequences

OS-I's direct-sum topology is characterized using the natural injection of each arity test space
into finite sequences. This module constructs the exact Mathlib-side injection: identify one
Schwartz test with the singleton finite stage and compose its continuous linear singleton-stage map
with the corresponding continuous linear stage extension.

The named topology and module instances are installed only locally. The resulting coordinate maps
are exact, injective, and continuously linear for the preliminary finite-stage topology. The OS-I
linear-map continuity criterion and identification with the printed locally convex direct sum remain
separate unproved comparisons.
-/

namespace YangMills

noncomputable local instance scalarFiniteSchwartzCoordinateTopologyLocal
    (d : EuclideanDimension) : TopologicalSpace (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzFiniteStageFinalTopology d

noncomputable local instance scalarFiniteSchwartzCoordinateAddCommGroupLocal
    (d : EuclideanDimension) : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceAddCommGroup d

noncomputable local instance scalarFiniteSchwartzCoordinateModuleLocal
    (d : EuclideanDimension) : Module ℂ (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceModule d

/-- Put one exact `n`-point Schwartz test into the singleton stage `{n}`. -/
noncomputable def scalarSchwartzToSingletonStage
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n) :
    ScalarFiniteSchwartzStage d {n} :=
  fun q => castScalarSchwartzArity
    (by simpa using (Finset.mem_singleton.mp q.property).symm) f

@[simp] theorem scalarSchwartzToSingletonStage_at_coordinate
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n) :
    scalarSchwartzToSingletonStage d n f ⟨n, by simp⟩ = f := by
  unfold scalarSchwartzToSingletonStage
  rw [castScalarSchwartzArity_rfl]

/-- The singleton-stage assignment is complex-linear. -/
noncomputable def scalarSchwartzToSingletonStageLinearMap
    (d : EuclideanDimension) (n : ℕ) :
    ScalarSchwartzTestFunction d n →ₗ[ℂ] ScalarFiniteSchwartzStage d {n} where
  toFun := scalarSchwartzToSingletonStage d n
  map_add' f g := by
    funext q
    rcases q with ⟨q, hq⟩
    simp only [Finset.mem_singleton] at hq
    subst q
    simp
  map_smul' c f := by
    funext q
    rcases q with ⟨q, hq⟩
    simp only [Finset.mem_singleton] at hq
    subst q
    simp

/-- The singleton-stage assignment is continuously complex-linear for the dependent product
Schwartz topology. -/
noncomputable def scalarSchwartzToSingletonStageContinuousLinearMap
    (d : EuclideanDimension) (n : ℕ) :
    ScalarSchwartzTestFunction d n →L[ℂ] ScalarFiniteSchwartzStage d {n} :=
  { scalarSchwartzToSingletonStageLinearMap d n with
    cont := by
      apply continuous_pi
      intro q
      rcases q with ⟨q, hq⟩
      simp only [Finset.mem_singleton] at hq
      subst q
      exact continuous_id }

/-- The exact natural coordinate injection into unrestricted finite Schwinger sequences. -/
noncomputable def scalarSchwartzCoordinateInjectionContinuousLinearMap
    (d : EuclideanDimension) (n : ℕ) :
    ScalarSchwartzTestFunction d n →L[ℂ] ScalarFiniteSchwartzSequence d :=
  (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d {n}).comp
    (scalarSchwartzToSingletonStageContinuousLinearMap d n)

/-- The injected test is retained exactly at its source arity. -/
@[simp] theorem scalarSchwartzCoordinateInjection_component_self
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).component n = f := by
  simp [scalarSchwartzCoordinateInjectionContinuousLinearMap,
    scalarSchwartzToSingletonStageContinuousLinearMap,
    scalarSchwartzToSingletonStageLinearMap]

/-- Every component outside the injected coordinate is exactly zero. -/
@[simp] theorem scalarSchwartzCoordinateInjection_component_ne
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n)
    (m : ℕ) (h : m ≠ n) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).component m = 0 := by
  rw [show scalarSchwartzCoordinateInjectionContinuousLinearMap d n f =
    scalarFiniteSchwartzStageToSequence d {n}
      (scalarSchwartzToSingletonStage d n f) by rfl]
  rw [scalarFiniteSchwartzStageToSequence_component]
  apply scalarFiniteSchwartzStageComponent_of_not_mem
  simpa

/-- The natural coordinate injection is injective, not a disconnected zero map. -/
theorem scalarSchwartzCoordinateInjection_injective
    (d : EuclideanDimension) (n : ℕ) :
    Function.Injective (scalarSchwartzCoordinateInjectionContinuousLinearMap d n) := by
  intro f g h
  have hcomponent := congrArg
    (fun q : ScalarFiniteSchwartzSequence d => q.component n) h
  simpa using hcomponent

/-- A nonzero source test has exact singleton support after coordinate injection. -/
theorem scalarSchwartzCoordinateInjection_support_eq_singleton
    (d : EuclideanDimension) (n : ℕ) (f : ScalarSchwartzTestFunction d n)
    (hnonzero : f ≠ 0) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).support = {n} := by
  ext m
  rw [(scalarSchwartzCoordinateInjectionContinuousLinearMap d n f).mem_support_iff]
  by_cases h : m = n
  · subst m
    simp [hnonzero]
  · simp [h]

/-- The zero source test has empty exact support after coordinate injection. -/
@[simp] theorem scalarSchwartzCoordinateInjection_zero_support
    (d : EuclideanDimension) (n : ℕ) :
    (scalarSchwartzCoordinateInjectionContinuousLinearMap d n
      (0 : ScalarSchwartzTestFunction d n)).support = ∅ := by
  ext m
  rw [(scalarSchwartzCoordinateInjectionContinuousLinearMap d n 0).mem_support_iff]
  by_cases h : m = n
  · subst m
    rw [scalarSchwartzCoordinateInjection_component_self]
    simp
  · rw [scalarSchwartzCoordinateInjection_component_ne d n 0 m h]
    simp

end YangMills
