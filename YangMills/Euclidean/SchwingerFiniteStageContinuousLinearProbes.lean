/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteStageContinuousLinear
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for continuous linear finite-stage maps

The probes expose exact named addition/scalar wiring, off-stage vanishing, continuity, support
containment, and recovery of the explicit nonzero bump through the bundled map.
-/

namespace YangMills.Euclidean.SchwingerFiniteStageContinuousLinear.Probes

/-- Bundled stage linearity uses the exact named sequence addition. -/
theorem exact_stage_add
    (d : EuclideanDimension) (s : Finset ℕ)
    (x y : ScalarFiniteSchwartzStage d s) :
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s (x + y) =
      addScalarFiniteSchwartzSequence d
        (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x)
        (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s y) := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  rw [scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component,
    addScalarFiniteSchwartzSequence_component,
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component,
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component]
  by_cases h : n ∈ s
  · simp [scalarFiniteSchwartzStageComponent, h]
  · simp [scalarFiniteSchwartzStageComponent, h]

/-- Bundled stage linearity uses the exact named complex scalar operation. -/
theorem exact_stage_smul
    (d : EuclideanDimension) (s : Finset ℕ) (c : ℂ)
    (x : ScalarFiniteSchwartzStage d s) :
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s (c • x) =
      smulScalarFiniteSchwartzSequence d c
        (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x) := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  rw [scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component,
    smulScalarFiniteSchwartzSequence_component,
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component]
  by_cases h : n ∈ s
  · simp [scalarFiniteSchwartzStageComponent, h]
  · simp [scalarFiniteSchwartzStageComponent, h]

/-- The bundled map is genuinely continuous for the named finite-stage final topology. -/
theorem exact_stage_map_continuous
    (d : EuclideanDimension) (s : Finset ℕ) :
    @Continuous (ScalarFiniteSchwartzStage d s) (ScalarFiniteSchwartzSequence d)
      inferInstance (scalarFiniteSchwartzFiniteStageFinalTopology d)
      (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s) := by
  letI : TopologicalSpace (ScalarFiniteSchwartzSequence d) :=
    scalarFiniteSchwartzFiniteStageFinalTopology d
  letI : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
    scalarFiniteSchwartzSequenceAddCommGroup d
  letI : Module ℂ (ScalarFiniteSchwartzSequence d) :=
    scalarFiniteSchwartzSequenceModule d
  exact (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s).continuous

/-- A bundled stage map still vanishes at every arity outside its stage. -/
theorem bundled_stage_outside_zero
    (d : EuclideanDimension) (s : Finset ℕ)
    (x : ScalarFiniteSchwartzStage d s) (n : ℕ) (h : n ∉ s) :
    (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x).component n = 0 := by
  rw [scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component]
  exact scalarFiniteSchwartzStageComponent_of_not_mem d s x n h

/-- Bundling cannot allow exact support to escape the chosen finite stage. -/
theorem bundled_stage_support_cannot_escape
    (d : EuclideanDimension) (s : Finset ℕ)
    (x : ScalarFiniteSchwartzStage d s) (n : ℕ)
    (hmem : n ∈ (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x).support) :
    n ∈ s :=
  scalarFiniteSchwartzStageToSequenceContinuousLinearMap_support_subset d s x hmem

/-- The explicit nonzero bump sequence is recovered through an actual bundled continuous linear
stage map, preventing a disconnected zero map. -/
theorem bundled_stage_recovers_singleton_bump
    (d : EuclideanDimension) :
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap d
        (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence.support
        (scalarFiniteSchwartzSequenceToSupportStage d
          (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence) =
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence :=
  scalarFiniteSchwartzStage_recover d
    (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence

/-- Recovery is nontrivial: arity one remains in the bundled bump output support. -/
theorem bundled_bump_one_mem_support
    (d : EuclideanDimension) :
    1 ∈ (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d
        (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence.support
        (scalarFiniteSchwartzSequenceToSupportStage d
          (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence)).support := by
  rw [bundled_stage_recovers_singleton_bump]
  rw [_root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.forgotten_singleton_bump_support]
  simp

end YangMills.Euclidean.SchwingerFiniteStageContinuousLinear.Probes
