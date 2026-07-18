/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteStageTopology
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for the finite-stage final topology

The probes ensure stage bounds do not become fake support, every exact sequence is reached by its
actual support stage, the explicit nonzero bump survives recovery, and continuity is controlled by
all finite-stage maps. The topology remains named and locally installed only.
-/

namespace YangMills.Euclidean.SchwingerFiniteStageTopology.Probes

/-- A stage entry inside the finite bound is the exact dependent component supplied there. -/
theorem inside_stage_component_is_exact
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s)
    (n : ℕ) (h : n ∈ s) :
    scalarFiniteSchwartzStageComponent d s x n = x ⟨n, h⟩ :=
  scalarFiniteSchwartzStageComponent_of_mem d s x n h

/-- Outside the finite stage, extension is exactly zero. -/
theorem outside_stage_component_is_zero
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s)
    (n : ℕ) (h : n ∉ s) :
    scalarFiniteSchwartzStageComponent d s x n = 0 :=
  scalarFiniteSchwartzStageComponent_of_not_mem d s x n h

/-- The finite stage is only a bound: output support still records exactly nonzero components. -/
theorem stage_support_is_exact
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s)
    (n : ℕ) :
    n ∈ (scalarFiniteSchwartzStageToSequence d s x).support ↔
      (scalarFiniteSchwartzStageToSequence d s x).component n ≠ 0 :=
  (scalarFiniteSchwartzStageToSequence d s x).mem_support_iff n

/-- Exact stage support cannot escape its chosen finite arity bound. -/
theorem stage_support_cannot_escape
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s)
    (n : ℕ) (hmem : n ∈ (scalarFiniteSchwartzStageToSequence d s x).support) :
    n ∈ s :=
  scalarFiniteSchwartzStageToSequence_support_subset d s x hmem

/-- Every unrestricted exact-support sequence is genuinely in the image of a finite stage. -/
theorem every_sequence_has_exact_stage_recovery
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    scalarFiniteSchwartzStageToSequence d f.support
      (scalarFiniteSchwartzSequenceToSupportStage d f) = f :=
  scalarFiniteSchwartzStage_recover d f

/-- Recovery retains the explicit singleton bump rather than collapsing all stages to zero. -/
theorem singleton_bump_stage_recovers_nonzero_sequence
    (d : EuclideanDimension) :
    scalarFiniteSchwartzStageToSequence d
        (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence.support
        (scalarFiniteSchwartzSequenceToSupportStage d
          (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence) =
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence :=
  scalarFiniteSchwartzStage_recover d
    (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence

/-- A stage filled with zero has empty exact support even when the chosen stage bound is nonempty. -/
theorem zero_stage_does_not_create_fake_support
    (d : EuclideanDimension) (s : Finset ℕ) :
    (scalarFiniteSchwartzStageToSequence d s
      (fun _ => 0 : ScalarFiniteSchwartzStage d s)).support = ∅ := by
  classical
  ext n
  simp [scalarFiniteSchwartzStageToSequence,
    scalarFiniteSchwartzStageComponent]

/-- Every stage map is continuous into the explicit named final topology. -/
theorem every_stage_map_is_continuous
    (d : EuclideanDimension) (s : Finset ℕ) :
    @Continuous (ScalarFiniteSchwartzStage d s) (ScalarFiniteSchwartzSequence d)
      inferInstance (scalarFiniteSchwartzFiniteStageFinalTopology d)
      (scalarFiniteSchwartzStageToSequence d s) :=
  continuous_scalarFiniteSchwartzStageToSequence d s

/-- A map out of the named topology is continuous exactly when all finite-stage composites are. -/
theorem exact_finite_stage_universal_property
    (d : EuclideanDimension) {Y : Type*} [TopologicalSpace Y]
    (g : ScalarFiniteSchwartzSequence d → Y) :
    @Continuous (ScalarFiniteSchwartzSequence d) Y
        (scalarFiniteSchwartzFiniteStageFinalTopology d) inferInstance g ↔
      ∀ s : Finset ℕ,
        Continuous (g ∘ scalarFiniteSchwartzStageToSequence d s) :=
  continuous_from_scalarFiniteSchwartzFiniteStageFinalTopology_iff d g

end YangMills.Euclidean.SchwingerFiniteStageTopology.Probes
