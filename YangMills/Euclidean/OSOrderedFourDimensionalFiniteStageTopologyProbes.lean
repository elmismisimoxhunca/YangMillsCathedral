/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageTopology

/-!
# Hostile probes for the exact OS source finite-stage final topology

The probes lock stage values, zero extension, exact support filtering, recovery, scalar separation
and the universal property. They do not call the topology OS-I's locally convex direct sum before
compatible vector-topological structure and comparison are proved.
-/

namespace YangMills.OSOrderedFourDimensionalFiniteStageTopology.Probes

noncomputable section

/-- A selected stage component is preserved exactly as the same source-space Schwartz function. -/
theorem exact_component_of_mem
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s)
    (arity : PositiveArity) (h : arity ∈ s) :
    ((osPositiveTimeOrderedFourDimensionalStageToSequence s x).component arity).toSchwartz =
      (x.2 ⟨arity, h⟩).toSchwartz := by
  simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
    osPositiveTimeOrderedFourDimensionalStageComponent, h]

/-- A component outside the selected stage is exactly zero in ambient Schwartz space. -/
theorem exact_component_of_not_mem
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s)
    (arity : PositiveArity) (h : arity ∉ s) :
    ((osPositiveTimeOrderedFourDimensionalStageToSequence s x).component arity).toSchwartz = 0 := by
  simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
    osPositiveTimeOrderedFourDimensionalStageComponent, h,
    zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
    OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- Stage support is filtered by actual nonvanishing and cannot retain an unrelated arity. -/
theorem exact_support_subset
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    (osPositiveTimeOrderedFourDimensionalStageToSequence s x).support ⊆ s :=
  osPositiveTimeOrderedFourDimensionalStageToSequence_support_subset s x

/-- Every source sequence, including its independent scalar, is recovered from actual support. -/
theorem exact_support_stage_recovery
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    osPositiveTimeOrderedFourDimensionalStageToSequence f.support
      (osPositiveTimeOrderedFourDimensionalSequenceToSupportStage f) = f :=
  osPositiveTimeOrderedFourDimensionalStage_recover f

/-- The empty positive stage can still carry the exact scalar unit; scalar data is not lost by
positive-support indexing. -/
theorem empty_stage_retains_scalar_unit :
    osPositiveTimeOrderedFourDimensionalStageToSequence ∅
      ((1 : ℂ), fun arity => False.elim (by
        have hempty : ∀ a : PositiveArity, a ∉ (∅ : Finset PositiveArity) := by decide
        exact hempty arity.val arity.property)) =
        unitZeroPointFourDimensionalOSSourceSequence := by
  apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
  · rfl
  · intro arity
    simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
      osPositiveTimeOrderedFourDimensionalStageComponent,
      unitZeroPointFourDimensionalOSSourceSequence,
      zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
      OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- Every finite-stage map is continuous for exactly the named final topology. -/
theorem exact_stage_continuity (s : Finset PositiveArity) :
    @Continuous (OSPositiveTimeOrderedFourDimensionalStage s)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology
      (osPositiveTimeOrderedFourDimensionalStageToSequence s) :=
  continuous_osPositiveTimeOrderedFourDimensionalStageToSequence s

/-- The named topology retains its exact all-stage universal property. -/
theorem exact_universal_property
    {Y : Type*} [TopologicalSpace Y]
    (g : OSPositiveTimeOrderedFourDimensionalTestSequence → Y) :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence Y
        osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology inferInstance g ↔
      ∀ s : Finset PositiveArity,
        Continuous (g ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s) :=
  continuous_from_osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology_iff g

end

end YangMills.OSOrderedFourDimensionalFiniteStageTopology.Probes
