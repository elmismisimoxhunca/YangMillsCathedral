/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteSequenceModule

/-!
# Continuous linear finite-stage maps for Schwinger sequences

The preliminary finite-stage final topology was defined before algebra was installed. This module
combines the named topology and named complex-module structures locally and upgrades every exact
finite-stage map to a continuous complex-linear map.

These declarations verify compatibility of each generating stage map only. They do not yet prove
that sequence addition or joint scalar multiplication is continuous, do not install a global
topological vector space, and do not identify the preliminary topology with OS-I's locally convex
direct sum or its linear coordinate-injection criterion.
-/

namespace YangMills

noncomputable local instance scalarFiniteSchwartzSequenceTopologyLocal
    (d : EuclideanDimension) : TopologicalSpace (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzFiniteStageFinalTopology d

noncomputable local instance scalarFiniteSchwartzSequenceAddCommGroupLocal
    (d : EuclideanDimension) : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceAddCommGroup d

noncomputable local instance scalarFiniteSchwartzSequenceModuleLocal
    (d : EuclideanDimension) : Module ℂ (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceModule d

/-- Every exact finite-stage extension is complex-linear for the named sequence module. -/
noncomputable def scalarFiniteSchwartzStageToSequenceLinearMap
    (d : EuclideanDimension) (s : Finset ℕ) :
    ScalarFiniteSchwartzStage d s →ₗ[ℂ] ScalarFiniteSchwartzSequence d where
  toFun := scalarFiniteSchwartzStageToSequence d s
  map_add' x y := by
    apply ScalarFiniteSchwartzSequence.ext
    intro n
    change (scalarFiniteSchwartzStageToSequence d s (x + y)).component n =
      (addScalarFiniteSchwartzSequence d
        (scalarFiniteSchwartzStageToSequence d s x)
        (scalarFiniteSchwartzStageToSequence d s y)).component n
    rw [addScalarFiniteSchwartzSequence_component]
    by_cases h : n ∈ s
    · simp [scalarFiniteSchwartzStageComponent, h]
    · simp [scalarFiniteSchwartzStageComponent, h]
  map_smul' c x := by
    apply ScalarFiniteSchwartzSequence.ext
    intro n
    change (scalarFiniteSchwartzStageToSequence d s (c • x)).component n =
      (smulScalarFiniteSchwartzSequence d c
        (scalarFiniteSchwartzStageToSequence d s x)).component n
    rw [smulScalarFiniteSchwartzSequence_component]
    by_cases h : n ∈ s
    · simp [scalarFiniteSchwartzStageComponent, h]
    · simp [scalarFiniteSchwartzStageComponent, h]

/-- Every generating finite-stage map is a continuous complex-linear map into the named preliminary
final topology. -/
noncomputable def scalarFiniteSchwartzStageToSequenceContinuousLinearMap
    (d : EuclideanDimension) (s : Finset ℕ) :
    ScalarFiniteSchwartzStage d s →L[ℂ] ScalarFiniteSchwartzSequence d :=
  { scalarFiniteSchwartzStageToSequenceLinearMap d s with
    cont := continuous_scalarFiniteSchwartzStageToSequence d s }

@[simp] theorem scalarFiniteSchwartzStageToSequenceContinuousLinearMap_apply
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s) :
    scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x =
      scalarFiniteSchwartzStageToSequence d s x :=
  rfl

@[simp] theorem scalarFiniteSchwartzStageToSequenceContinuousLinearMap_component
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s)
    (n : ℕ) :
    (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x).component n =
      scalarFiniteSchwartzStageComponent d s x n :=
  rfl

/-- The bundled continuous linear stage map retains the exact support bound. -/
theorem scalarFiniteSchwartzStageToSequenceContinuousLinearMap_support_subset
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s) :
    (scalarFiniteSchwartzStageToSequenceContinuousLinearMap d s x).support ⊆ s :=
  scalarFiniteSchwartzStageToSequence_support_subset d s x

end YangMills
